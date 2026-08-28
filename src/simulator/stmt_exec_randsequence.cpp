#include <cmath>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_exec_internal.h"

namespace delta {

ExecTask ExecRandcase(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  // §18.16: each branch's weight expression is evaluated at most once, in
  // declaration order. Cache the drawn weights so a side-effecting expression
  // runs a single time and the same value feeds both the sum and the
  // selection. Weights are summed as unsigned values.
  std::vector<uint64_t> weights;
  weights.reserve(stmt->randcase_items.size());
  uint64_t total_weight = 0;
  for (const auto& item : stmt->randcase_items) {
    uint64_t w = EvalExpr(item.first, ctx, arena).ToUint64();
    weights.push_back(w);
    total_weight += w;
  }
  if (total_weight == 0) {
    ctx.GetDiag().Warning(stmt->range.start,
                          "randcase: all weights are zero; no branch selected",
                          Subclause("18.16"));
    co_return StmtResult::kDone;
  }

  // §18.16: one random number in [0, sum); branches are selected in
  // declaration order, with smaller numbers landing on the earlier (top)
  // weights. A zero-weight branch leaves the cumulative total unchanged and so
  // can never be selected. A sum wider than 32 bits cannot be covered by a
  // single 32-bit draw, so compose the random number from more than one draw
  // to reach the full [0, sum) range.
  uint64_t pick = 0;
  if (total_weight > 0xFFFFFFFFull) {
    uint64_t hi = ctx.Urandom32();
    uint64_t lo = ctx.Urandom32();
    pick = ((hi << 32) | lo) % total_weight;
  } else {
    pick = ctx.Urandom32() % total_weight;
  }
  uint64_t cumulative = 0;
  for (size_t i = 0; i < stmt->randcase_items.size(); ++i) {
    cumulative += weights[i];
    if (pick < cumulative) {
      co_return co_await ExecStmt(stmt->randcase_items[i].second, ctx, arena);
    }
  }
  co_return StmtResult::kDone;
}

namespace {
// §18.17.7: the implicit variables one rule declares for the value-returning
// productions it names. `total` holds how many times the rule names each such
// production, which decides whether its implicit variable is the scalar named
// after the production or an element of an array indexed 1..N, and `ordinal`
// gives each appearance its 1-based index in that array. The index is fixed by
// where the appearance is written and not by when it generates: §18.17.7 says
// of `if (cond) D(5) else D(20)` that the first element takes D(5)'s value and
// the second D(20)'s, so the else branch writes the second element even when it
// is the only branch that generated.
struct RuleValueCapture {
  std::unordered_map<std::string_view, int> total;
  std::unordered_map<const RsProductionItem*, int> ordinal;
};

// §18.17.7: one appearance of a value-returning production within a rule. name
// is the production's name, idx the 1-based ordinal of this appearance, and
// total how many times the rule names the production: a total above one means
// the implicit variable is the idx-th element of a 1..N array, a total of one
// means the scalar named after the production. An idx of zero means the rule
// declares no implicit variable for this generation.
struct RuleProductionSlot {
  std::string_view name;
  int idx;
  int total;
};
}  // namespace

static ExecTask ExecRsProduction(const Stmt* stmt, const RsProductionItem& call,
                                 SimContext& ctx, Arena& arena,
                                 RuleValueCapture* cap);

// §18.17.7: the rand join generation below declares and writes the implicit
// variables of the rules it interleaves, so it calls these four ahead of their
// definitions, which stand with the rest of the value-passing code at the end
// of this file.
static RuleValueCapture BuildRuleValueCapture(const Stmt* stmt,
                                              const RsRule& selected,
                                              SimContext& ctx);
static RuleValueCapture BuildStepValueCapture(
    const Stmt* stmt, const std::vector<const RsProd*>& steps, SimContext& ctx);
static RuleProductionSlot SlotForAppearance(const RuleValueCapture* cap,
                                            const RsProductionItem& call,
                                            std::string_view name);
static void StoreRuleProductionValue(const RuleProductionSlot& slot,
                                     const RsProduction* child,
                                     const Logic4Vec& ret_value,
                                     SimContext& ctx, Arena& arena);

static const RsProduction* FindProduction(const Stmt* stmt,
                                          std::string_view name) {
  for (const auto& prod : stmt->rs_productions) {
    if (prod.name == name) return &prod;
  }
  return nullptr;
}

// §18.17.7: a production yields a readable value only when it declares a
// non-void return type. A production with no return type assumes a void return
// type, so it contributes no implicit variable.
static bool ProductionReturnsValue(const RsProduction* p) {
  return p != nullptr && p->has_return_type &&
         p->return_type.kind != DataTypeKind::kVoid;
}

// §18.17.7: reports whether a production returns a string. §6.16 gives a
// string no declared width: it is as wide as the characters it holds, and one
// that was never written is "", the empty string, of zero length. Storage for
// such a value is therefore sized by what was returned, and not by the 32-bit
// carrier every other return type with no computable width falls back to.
static bool ProductionReturnsString(const RsProduction* p) {
  return p != nullptr && p->has_return_type &&
         p->return_type.kind == DataTypeKind::kString;
}

static ExecTask ExecRsProd(const Stmt* stmt, const RsProd& prod,
                           SimContext& ctx, Arena& arena,
                           RuleValueCapture* cap);

static ExecTask ExecRsProdIf(const Stmt* stmt, const RsProd& prod,
                             SimContext& ctx, Arena& arena,
                             RuleValueCapture* cap) {
  if (EvalExpr(prod.condition, ctx, arena).ToUint64() != 0) {
    co_return co_await ExecRsProduction(stmt, prod.if_true, ctx, arena, cap);
  }
  if (prod.has_else) {
    co_return co_await ExecRsProduction(stmt, prod.if_false, ctx, arena, cap);
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecRsProdRepeat(const Stmt* stmt, const RsProd& prod,
                                 SimContext& ctx, Arena& arena,
                                 RuleValueCapture* cap) {
  auto count = EvalExpr(prod.repeat_count, ctx, arena).ToUint64();
  for (uint64_t i = 0; i < count; ++i) {
    auto result =
        co_await ExecRsProduction(stmt, prod.repeat_item, ctx, arena, cap);
    if (result == StmtResult::kBreak) co_return StmtResult::kBreak;
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecRsProdCase(const Stmt* stmt, const RsProd& prod,
                               SimContext& ctx, Arena& arena,
                               RuleValueCapture* cap) {
  // 18.17.3: evaluate the case expression once, then compare it against each
  // case item expression in the order written. Items separated by commas share
  // a production, so any pattern matching wins for that item. The first item
  // whose expression matches generates its production. The default item is a
  // fallback used only when no case item expression matches, regardless of
  // where it appears in the list, so remember it and resolve it after the scan.
  auto val = EvalExpr(prod.case_expr, ctx, arena).ToUint64();
  const RsCaseItem* default_item = nullptr;
  for (const auto& ci : prod.case_items) {
    if (ci.is_default) {
      if (!default_item) default_item = &ci;
      continue;
    }
    for (auto* pat : ci.patterns) {
      if (EvalExpr(pat, ctx, arena).ToUint64() == val) {
        co_return co_await ExecRsProduction(stmt, ci.item, ctx, arena, cap);
      }
    }
  }
  if (default_item) {
    co_return co_await ExecRsProduction(stmt, default_item->item, ctx, arena,
                                        cap);
  }
  co_return StmtResult::kDone;
}

// 18.17: every code block inside a randsequence is its own anonymous automatic
// scope. Variables it declares are recreated on each execution and do not leak
// to sibling code blocks or outlive the block, so we bracket the statements
// with a fresh automatic scope.
static ExecTask ExecRsProdCodeBlock(const RsProd& prod, SimContext& ctx,
                                    Arena& arena) {
  ctx.PushScope();
  StmtResult block_result = StmtResult::kDone;
  for (auto* s : prod.code_stmts) {
    auto result = co_await ExecStmt(s, ctx, arena);
    if (result == StmtResult::kBreak || result == StmtResult::kReturn) {
      block_result = result;
      break;
    }
  }
  ctx.PopScope();
  co_return block_result;
}

static ExecTask ExecRsProd(const Stmt* stmt, const RsProd& prod,
                           SimContext& ctx, Arena& arena,
                           RuleValueCapture* cap) {
  switch (prod.kind) {
    case RsProdKind::kCodeBlock:
      co_return co_await ExecRsProdCodeBlock(prod, ctx, arena);
    case RsProdKind::kItem:
      co_return co_await ExecRsProduction(stmt, prod.item, ctx, arena, cap);
    case RsProdKind::kIf:
      co_return co_await ExecRsProdIf(stmt, prod, ctx, arena, cap);
    case RsProdKind::kRepeat:
      co_return co_await ExecRsProdRepeat(stmt, prod, ctx, arena, cap);
    case RsProdKind::kCase:
      co_return co_await ExecRsProdCase(stmt, prod, ctx, arena, cap);
  }
  co_return StmtResult::kDone;
}

// §18.17.1: "Weight expressions are evaluated when their enclosing production
// is selected, thus allowing weights to change dynamically." One selection
// evaluates each rule's weight once, so cache the drawn weights before summing
// and walk the cached values: rs_weight_specification admits a parenthesized
// expression and so a function call, and a second evaluation would perform that
// call's effect twice and let the cumulative walk run against numbers other
// than the ones the total was drawn from. §18.16 states the same rule for the
// sibling randcase statement in as many words: "Each weight expression is
// evaluated at most once (implementations can cache identical expressions) in
// an unspecified order." A rule that specifies no weight counts 1, which is
// what §18.17.1 makes the weight of a production list written without ':='.
static const RsRule& SelectRule(const RsProduction& production, SimContext& ctx,
                                Arena& arena) {
  if (production.rules.size() <= 1) return production.rules[0];
  std::vector<uint64_t> weights;
  weights.reserve(production.rules.size());
  uint64_t total_weight = 0;
  for (const auto& rule : production.rules) {
    uint64_t w = rule.weight ? EvalExpr(rule.weight, ctx, arena).ToUint64() : 1;
    weights.push_back(w);
    total_weight += w;
  }
  if (total_weight == 0) return production.rules[0];
  uint64_t pick = ctx.Urandom32() % total_weight;

  // §18.17.1: the probability of a production list being generated is
  // proportional to its weight, so the draw lands in the interval each rule's
  // weight spans and a zero-weight rule spans no interval and is never
  // selected. Summing the cached weights again reaches total_weight exactly,
  // and pick is below total_weight, so the draw is always covered: the last
  // rule covers whatever the rules before it do not, and is returned without a
  // test rather than as a fallback for a walk that cannot run out.
  uint64_t cumulative = 0;
  for (size_t i = 0; i + 1 < production.rules.size(); ++i) {
    cumulative += weights[i];
    if (pick < cumulative) return production.rules[i];
  }
  return production.rules.back();
}

// 18.17.5: the optional weight following the rand join keywords states, as a
// real value, how strongly the remaining length of each operand sequence biases
// which sequence advances next. The standard constrains it to [0.0, 1.0], so
// clamp any out of range value to that interval, and use the neutral 0.5 when
// the expression is omitted.
static double EvalRandJoinBias(Expr* expr, SimContext& ctx, Arena& arena) {
  if (!expr) return 0.5;
  auto v = EvalExpr(expr, ctx, arena);
  double f = v.is_real ? RealVecToDouble(v) : static_cast<double>(v.ToUint64());
  if (f < 0.0) f = 0.0;
  if (f > 1.0) f = 1.0;
  return f;
}

namespace {
// One operand of a rand join, expanded one level (to depth 1) into the
// production items it will contribute. The interleaver emits these items in
// order; cursor marks how many have already been generated.
//
// §18.17.7: item is the appearance the enclosing rand join rule wrote, which
// fixes which implicit variable of that rule this operand writes; production is
// what the appearance names; ret_value is the storage a return statement in the
// operand assigns to; and cap holds the implicit variables of the operand's own
// rule, since steps generates the productions that rule names.
struct RandJoinSeq {
  std::vector<const RsProd*> steps;
  size_t cursor = 0;
  const RsProductionItem* item = nullptr;
  const RsProduction* production = nullptr;
  RuleValueCapture cap;
  Logic4Vec ret_value;
  bool returns_value = false;
  size_t Remaining() const { return steps.size() - cursor; }
};
}  // namespace

// 18.17.5: expanding an operand to depth 1 yields the production items of its
// selected rule. A nested rand join contributes its own operands as the
// depth-1 items, so wrap each in a production item step.
static void CollectRandJoinSteps(const RsRule& rule, Arena& arena,
                                 std::vector<const RsProd*>& steps) {
  if (rule.is_rand_join) {
    for (const auto& item : rule.rand_join_items) {
      auto* p = arena.Create<RsProd>();
      p->kind = RsProdKind::kItem;
      p->item = item;
      steps.push_back(p);
    }
    return;
  }
  for (const auto& prod : rule.prods) steps.push_back(&prod);
}

// 18.17.5: at each step choose one operand and emit its next production. A
// sequence's length is the number of productions it has not yet contributed.
// The bias maps to an exponent on that length: 0.5 (exponent 1) keeps the
// choice proportional to remaining length so no length is prioritized, values
// toward 0.0 (negative exponent) favor the shortest remaining sequences, and
// values toward 1.0 favor the longest. Returns seqs.size() when every operand
// sequence has been drained.
static size_t ChooseRandJoinOperand(const std::vector<RandJoinSeq>& seqs,
                                    double exponent, SimContext& ctx) {
  double total = 0.0;
  for (const auto& seq : seqs) {
    if (seq.Remaining() > 0)
      total += std::pow(static_cast<double>(seq.Remaining()), exponent);
  }
  if (total <= 0.0)
    return seqs.size();  // every operand sequence has been drained

  double draw = (ctx.Urandom32() / 4294967296.0) * total;
  double cumulative = 0.0;
  size_t chosen = seqs.size();
  for (size_t i = 0; i < seqs.size(); ++i) {
    if (seqs[i].Remaining() == 0) continue;
    cumulative += std::pow(static_cast<double>(seqs[i].Remaining()), exponent);
    if (draw < cumulative) {
      chosen = i;
      break;
    }
  }
  if (chosen == seqs.size()) {
    // Floating point rounding can leave draw just past the running total;
    // fall back to the last operand that still has productions to emit.
    for (size_t i = seqs.size(); i-- > 0;) {
      if (seqs[i].Remaining() > 0) {
        chosen = i;
        break;
      }
    }
  }
  return chosen;
}

// 18.17.5: run one operand rule's weight code in declaration order. A break
// must propagate out and abort the whole interleaving (signalled via the
// returned StmtResult); a return only aborts this rule's contribution, leaving
// rule_aborted set so the caller emits no steps for it.
static ExecTask RunRandJoinRuleWeightCode(const RsRule& rule, SimContext& ctx,
                                          Arena& arena, bool& rule_aborted) {
  for (auto* s : rule.weight_code) {
    auto r = co_await ExecStmt(s, ctx, arena);
    if (r == StmtResult::kBreak) co_return StmtResult::kBreak;
    if (r == StmtResult::kReturn) {
      rule_aborted = true;
      break;
    }
  }
  co_return StmtResult::kDone;
}

namespace {
// 18.17: the randsequence execution environment threaded through the generation
// helpers: the randsequence statement that owns the production declarations,
// the simulator context the productions run in, and the arena their run-time
// values and names are allocated from. Bundles the {stmt, ctx, arena} trio that
// recurs throughout this file into the single entity it describes.
struct RandseqEngine {
  const Stmt* stmt;
  SimContext& ctx;
  Arena& arena;
};
}  // namespace

// 18.17.5: expand one rand join operand to depth 1 into its production-item
// steps. Selects the operand's rule, runs that rule's weight code, and (unless
// the rule returned) collects its steps into seq. A break in the weight code is
// surfaced via the returned StmtResult so the caller can abort the whole join.
//
// §18.17.7: record what the operand names and size the storage its generation
// returns into, and declare the implicit variables of the rule the steps came
// from, because those steps are what generates the productions that rule names.
static ExecTask BuildOneRandJoinSeq(const RandseqEngine& eng,
                                    const RsProductionItem& item,
                                    RandJoinSeq& seq) {
  const auto* production = FindProduction(eng.stmt, item.name);
  if (!production) co_return StmtResult::kDone;
  seq.item = &item;
  seq.production = production;
  seq.returns_value = ProductionReturnsValue(production);
  if (seq.returns_value) {
    // §6.16: a string has no declared width and starts as "", so leave its
    // storage empty; every other return type EvalTypeWidth gives no width to
    // keeps the 32-bit carrier, as ExecRsProduction sizes it.
    uint32_t w = EvalTypeWidth(production->return_type);
    if (w == 0 && !ProductionReturnsString(production)) w = 32;
    seq.ret_value = MakeLogic4VecVal(eng.arena, w, 0);
  }
  const auto& rule = SelectRule(*production, eng.ctx, eng.arena);
  bool rule_aborted = false;
  auto r = co_await RunRandJoinRuleWeightCode(rule, eng.ctx, eng.arena,
                                              rule_aborted);
  if (r == StmtResult::kBreak) co_return StmtResult::kBreak;
  if (rule_aborted) co_return StmtResult::kDone;
  CollectRandJoinSteps(rule, eng.arena, seq.steps);
  seq.cap = BuildStepValueCapture(eng.stmt, seq.steps, eng.ctx);
  co_return StmtResult::kDone;
}

// 18.17.5: expand each rand join operand one level into the production items of
// its selected rule, running that rule's weight code in declaration order
// first. A rule whose weight code breaks aborts the whole interleaving; one
// that returns contributes no steps. Returns false (with abort set) when a
// break must propagate out of the caller.
static ExecTask BuildRandJoinSeqs(const RandseqEngine& eng,
                                  const RsRule& selected,
                                  std::vector<RandJoinSeq>& seqs,
                                  bool& aborted) {
  seqs.reserve(selected.rand_join_items.size());
  for (const auto& item : selected.rand_join_items) {
    RandJoinSeq seq;
    auto r = co_await BuildOneRandJoinSeq(eng, item, seq);
    if (r == StmtResult::kBreak) {
      aborted = true;
      co_return StmtResult::kBreak;
    }
    seqs.push_back(std::move(seq));
  }
  co_return StmtResult::kDone;
}

// §18.17.7: generate one production of one rand join operand, with a return
// statement inside it assigning to that operand's own storage. §18.17.5
// interleaves the operands, so more than one of them is part-generated at any
// moment and a single shared return slot would let one operand's return
// statement write another operand's value. An operand of void return type holds
// no slot at all, for the reason ExecRsProduction gives: the return statement
// assigns its expression to the production whose code block holds it.
//
// The steps generate the productions the operand's own rule names, so they are
// given that rule's implicit variables and not the enclosing rand join rule's.
static ExecTask ExecOneRandJoinStep(const RandseqEngine& eng,
                                    RandJoinSeq& seq) {
  const RsProd* step = seq.steps[seq.cursor++];
  Logic4Vec* prev_slot =
      eng.ctx.SetRsReturnSlot(seq.returns_value ? &seq.ret_value : nullptr);
  auto result =
      co_await ExecRsProd(eng.stmt, *step, eng.ctx, eng.arena, &seq.cap);
  eng.ctx.SetRsReturnSlot(prev_slot);
  co_return result;
}

// §18.17.7: write the implicit variable this operand of a rand join rule
// declares, once the operand has generated the last production it contributed.
// Which element it writes is fixed by where the operand is written and not by
// when it generated: the clause assigns "the elements of the array ... the
// values returned by the instances of the production according to the syntactic
// order of appearance", and §18.17.5 reorders generation alone. The clause
// already reads that way for the ordinary productions, giving the code block of
// `if (cond) D(5) else D(20)` an `int D[1:2]` whose second element the else
// branch writes when it is the only branch that generated.
static void StoreRandJoinOperandValue(const RandJoinSeq& seq,
                                      const RuleValueCapture& cap,
                                      SimContext& ctx, Arena& arena) {
  if (!seq.returns_value) return;
  RuleProductionSlot slot =
      SlotForAppearance(&cap, *seq.item, seq.production->name);
  if (slot.idx == 0) return;
  // §6.16: a string cannot hold the "\0" character, so an integral expression
  // returned by a string production loses the zero bytes of its own width.
  // ExecRsProduction strips them on the ordinary path for the same reason.
  Logic4Vec value = ProductionReturnsString(seq.production)
                        ? StripStringZeros(seq.ret_value, arena)
                        : seq.ret_value;
  StoreRuleProductionValue(slot, seq.production, value, ctx, arena);
}

static ExecTask ExecRandJoinItems(const Stmt* stmt, const RsRule& selected,
                                  SimContext& ctx, Arena& arena) {
  // 18.17.5: rand join randomly interleaves its operand sequences while keeping
  // the productions within each operand in their original relative order. Each
  // operand is first expanded one level (depth 1) into the production items of
  // its selected rule; those items are the units that get interleaved.
  double bias = EvalRandJoinBias(selected.rand_join_expr, ctx, arena);

  // §18.17.7: a rand join rule is a rule, so it declares an implicit variable
  // for each of the productions it names that returns a value. Syntax 18-13
  // writes those productions after the rand join keywords, and they are
  // declared before any of them generates so that a production named more than
  // once is an array from the start.
  RuleValueCapture cap = BuildRuleValueCapture(stmt, selected, ctx);

  std::vector<RandJoinSeq> seqs;
  bool aborted = false;
  RandseqEngine eng{stmt, ctx, arena};
  auto build = co_await BuildRandJoinSeqs(eng, selected, seqs, aborted);
  if (aborted) co_return build;

  double exponent = 4.0 * bias - 1.0;
  for (;;) {
    size_t chosen = ChooseRandJoinOperand(seqs, exponent, ctx);
    if (chosen == seqs.size()) break;

    auto result = co_await ExecOneRandJoinStep(eng, seqs[chosen]);
    if (result == StmtResult::kBreak) co_return StmtResult::kBreak;
    if (result == StmtResult::kReturn) {
      // 18.17.6: return aborts the current production; drop the remainder of
      // this operand's sequence and keep interleaving the others.
      seqs[chosen].cursor = seqs[chosen].steps.size();
    }
    // §18.17.7: only the return value of a production already generated can be
    // read, so the operand's value is written the moment the last production it
    // contributed has generated.
    if (seqs[chosen].Remaining() == 0) {
      StoreRandJoinOperandValue(seqs[chosen], cap, ctx, arena);
    }
  }
  co_return StmtResult::kDone;
}

// §18.17.7: record one appearance of a value-returning production, giving it
// the next ordinal in the rule. Every appearance counts, including one written
// inside an if, repeat or case production: the clause gives the code block of
// `if (cond) D(5) else D(20)` the implicit declaration `int D[1:2]`, and the
// code block of `B repeat(5) C B` the declarations `int B[1:2]` and `int C`.
// A repeat counts its item once however many times it goes on to generate it.
static void CountRuleProductionItem(const Stmt* stmt,
                                    const RsProductionItem& item,
                                    RuleValueCapture& cap) {
  if (!ProductionReturnsValue(FindProduction(stmt, item.name))) return;
  cap.ordinal[&item] = ++cap.total[item.name];
}

// §18.17.7: count the appearances of every value-returning production one
// production of a rule names, reaching the items an if, repeat or case
// production generates as well as an item written directly in the rule.
static void CountRuleProductions(const Stmt* stmt, const RsProd& prod,
                                 RuleValueCapture& cap) {
  switch (prod.kind) {
    case RsProdKind::kItem:
      CountRuleProductionItem(stmt, prod.item, cap);
      return;
    case RsProdKind::kIf:
      CountRuleProductionItem(stmt, prod.if_true, cap);
      if (prod.has_else) CountRuleProductionItem(stmt, prod.if_false, cap);
      return;
    case RsProdKind::kRepeat:
      CountRuleProductionItem(stmt, prod.repeat_item, cap);
      return;
    case RsProdKind::kCase:
      for (const auto& ci : prod.case_items)
        CountRuleProductionItem(stmt, ci.item, cap);
      return;
    case RsProdKind::kCodeBlock:
      return;
  }
}

// §18.17.7: register the array shape of every production the counted
// appearances name more than once, so a code block can read an element before
// any generation has written one. A production named once needs no shape: its
// implicit variable is the scalar StoreRuleProductionValue creates.
static void RegisterRuleValueArrays(const Stmt* stmt,
                                    const RuleValueCapture& cap,
                                    SimContext& ctx) {
  for (const auto& [name, n] : cap.total) {
    if (n <= 1) continue;
    const auto* child = FindProduction(stmt, name);
    ArrayInfo info;
    info.lo = 1;
    info.size = static_cast<uint32_t>(n);
    uint32_t w = EvalTypeWidth(child->return_type);
    // §18.17.7: "the type is an array where the element type is the return
    // type of the production", so record the return type's kind for a read of
    // an element to consult. §6.16 then makes the element of a string array
    // that no generation wrote "", the empty string, rather than 32 bits of x;
    // every other return type EvalTypeWidth gives no width to keeps the
    // 32-bit carrier.
    info.elem_type_kind = child->return_type.kind;
    info.elem_width = w ? w : (ProductionReturnsString(child) ? 0 : 32);
    // §18.17: "The randsequence statement creates an automatic scope", and
    // §18.17.7 declares this array "within a rule", so the name stands for the
    // array only while that scope is on the stack. RegisterLocalArray puts the
    // shape in the same scope as the implicit variables
    // StoreRuleProductionValue creates, so PopScope takes both away together: a
    // variable of the design that shares the name is read as itself again once
    // the statement ends, and each activation of the rule sees its own shape.
    // §18.17.7's Example 2 needs the last of those, giving one production three
    // rules that name C once, twice and three times.
    ctx.RegisterLocalArray(name, info);
  }
}

// §18.17.7: within a rule, a variable is implicitly declared for each
// value-returning production the rule names. A production named once yields a
// scalar named after the production; a production named more than once yields
// an array indexed 1..N, with element i holding the value returned by the i-th
// appearance in syntactic order. Count the rule's appearances so a multiply
// appearing production can be registered as an array before any code block
// reads an element of it.
static RuleValueCapture BuildRuleValueCapture(const Stmt* stmt,
                                              const RsRule& selected,
                                              SimContext& ctx) {
  RuleValueCapture cap;
  // Syntax 18-13 gives a rand join rule its productions as the
  // rs_production_items written after the keywords, which stand in
  // RsRule::rand_join_items and in no RsProd of RsRule::prods. A rule holds one
  // list or the other, so both are walked and the empty one contributes
  // nothing.
  for (const auto& item : selected.rand_join_items) {
    CountRuleProductionItem(stmt, item, cap);
  }
  for (const auto& prod : selected.prods) {
    CountRuleProductions(stmt, prod, cap);
  }
  RegisterRuleValueArrays(stmt, cap, ctx);
  return cap;
}

// §18.17.5 interleaves a rand join operand's productions to a depth of 1, so
// what generates under the operand is the productions its own rule names rather
// than the operand itself. Count the appearances over the steps that expansion
// produced: for a nested rand join rule those are the wrappers
// CollectRandJoinSteps built around its operands, and the wrapper is what
// SlotForAppearance is given to look up.
static RuleValueCapture BuildStepValueCapture(
    const Stmt* stmt, const std::vector<const RsProd*>& steps,
    SimContext& ctx) {
  RuleValueCapture cap;
  for (const auto* step : steps) {
    CountRuleProductions(stmt, *step, cap);
  }
  RegisterRuleValueArrays(stmt, cap, ctx);
  return cap;
}

// §18.17.7: the implicit variable this appearance of a production writes. An
// appearance the rule recorded no ordinal for writes none: the top-level
// production the randsequence statement names stands in no rule, and a
// production that returns no value declares no variable to write.
static RuleProductionSlot SlotForAppearance(const RuleValueCapture* cap,
                                            const RsProductionItem& call,
                                            std::string_view name) {
  if (cap == nullptr) return RuleProductionSlot{name, 0, 0};
  auto ord = cap->ordinal.find(&call);
  if (ord == cap->ordinal.end()) return RuleProductionSlot{name, 0, 0};
  auto total = cap->total.find(name);
  return RuleProductionSlot{name, ord->second,
                            total == cap->total.end() ? 1 : total->second};
}

// §18.17.7: create the implicit variable that holds a generated production's
// return value. A production named more than once in the rule writes the
// idx-th element of its 1..N array, whose name is built at run time and so must
// be interned in the arena (the scope map keys on a stable string_view); a
// production named once writes the scalar named after the production. The name
// the variable was created under is reported through `created_name`; it
// outlives the call in both forms, so a caller that has to name the variable
// again does not have to rebuild the name.
static Variable* CreateRuleProductionVariable(const RuleProductionSlot& slot,
                                              uint32_t width, SimContext& ctx,
                                              Arena& arena,
                                              std::string_view* created_name) {
  if (slot.total > 1) {
    auto name = std::string(slot.name) + "[" + std::to_string(slot.idx) + "]";
    const std::string& interned = *arena.Create<std::string>(std::move(name));
    *created_name = interned;
    return ctx.CreateLocalVariable(interned, width);
  }
  *created_name = slot.name;
  return ctx.CreateLocalVariable(slot.name, width);
}

// §18.17.7: store one generated production's return value into its implicit
// variable, at the moment it is generated so that a code block written to its
// right observes the value and one written to its left does not.
static void StoreRuleProductionValue(const RuleProductionSlot& slot,
                                     const RsProduction* child,
                                     const Logic4Vec& ret_value,
                                     SimContext& ctx, Arena& arena) {
  uint32_t w = EvalTypeWidth(child->return_type);
  if (w == 0) w = ret_value.width;
  // §6.16: a string is as wide as the characters it holds, so a string
  // production that returned nothing leaves the empty string and not 32 bits
  // of zero. Every other return type EvalTypeWidth gives no width to keeps the
  // 32-bit carrier.
  if (w == 0 && !ProductionReturnsString(child)) w = 32;
  std::string_view created_name;
  Variable* var =
      CreateRuleProductionVariable(slot, w, ctx, arena, &created_name);
  var->value = ret_value;
  // §18.17.7 gives the implicit variable the production's return type, and
  // what reads a string reads SimContext::IsStringVariable rather than the
  // width, so register the name the variable was created under. The registry
  // keys on a string_view it never erases, and both names
  // CreateRuleProductionVariable reports outlive this call.
  if (ProductionReturnsString(child)) ctx.RegisterStringVariable(created_name);
}

static ExecTask ExecRuleProds(const Stmt* stmt, const RsRule& selected,
                              SimContext& ctx, Arena& arena) {
  // §18.17.7: only the return values of productions already generated (to the
  // left of a code block) are available. Each generation stores its value into
  // the implicit variable as it finishes, so a later code block observes it
  // while an earlier one does not.
  RuleValueCapture cap = BuildRuleValueCapture(stmt, selected, ctx);
  for (const auto& prod : selected.prods) {
    auto result = co_await ExecRsProd(stmt, prod, ctx, arena, &cap);
    if (result == StmtResult::kBreak) co_return StmtResult::kBreak;
    // §18.17.6: a return aborts the generation of the current production, so
    // the productions written after this one are not generated. Surface the
    // abort rather than reporting a normal completion, because the rule's own
    // code block is not generated either; ExecRsProduction turns it back into a
    // normal completion once the aborted production has finished.
    if (result == StmtResult::kReturn) co_return StmtResult::kReturn;
  }
  co_return StmtResult::kDone;
}

// §18.17.7: generate the rule's production list, then run the rs_code_block
// Syntax 18-14 writes after the rs_weight_specification. The clause reads that
// block against what stands to its left -- "Only the return values of
// productions already generated (i.e., to the left of the code block accessing
// them) can be retrieved" -- and the whole production list is written to its
// left. §18.17.7's own GenQueue example needs exactly that, giving the rule
// `LIST ITEM := 8 { q = { q, ITEM }; }` a code block that reads ITEM, a
// value-returning production of that same rule. A rand join rule is the case
// with nothing else: Syntax 18-18 admits only rs_production_items after the
// keywords, so this is the one code block such a rule can hold.
//
// §18.17.6 leaves break and return doing what they do from any code block: a
// break here terminates the randsequence, and a return aborts the current
// production, which by this point has finished generating its list. A list that
// broke or was itself aborted never reaches the block, an aborted production
// having nothing further to generate.
static ExecTask ExecSelectedRule(const Stmt* stmt, const RsRule& selected,
                                 SimContext& ctx, Arena& arena) {
  StmtResult prods_result = StmtResult::kDone;
  if (selected.is_rand_join) {
    prods_result = co_await ExecRandJoinItems(stmt, selected, ctx, arena);
  } else {
    prods_result = co_await ExecRuleProds(stmt, selected, ctx, arena);
  }
  if (prods_result != StmtResult::kDone) co_return prods_result;
  for (auto* s : selected.weight_code) {
    auto result = co_await ExecStmt(s, ctx, arena);
    if (result == StmtResult::kBreak || result == StmtResult::kReturn) {
      co_return result;
    }
  }
  co_return StmtResult::kDone;
}

// §18.17.7: passing data to a production uses the same syntax as a task call.
// Evaluate the actual arguments in the caller's scope, before the production's
// own scope is entered, sizing each to its formal's declared width.
static std::vector<Logic4Vec> EvalProductionActuals(
    const RsProduction* production, const RsProductionItem& call,
    SimContext& ctx, Arena& arena) {
  std::vector<Logic4Vec> actuals;
  actuals.reserve(call.args.size());
  for (size_t i = 0; i < call.args.size(); ++i) {
    uint32_t w = i < production->ports.size()
                     ? EvalTypeWidth(production->ports[i].data_type)
                     : 0;
    actuals.push_back(EvalExpr(call.args[i], ctx, arena, w));
  }
  return actuals;
}

// §18.17.7: a production creates a scope that encompasses all its rules and
// code blocks; formal arguments bound here are therefore available throughout
// the production. Bind each formal by position, falling back to its default
// value, then to zero, when no actual is supplied. The caller must have entered
// the production's scope.
static void BindProductionFormals(const RsProduction* production,
                                  const std::vector<Logic4Vec>& actuals,
                                  SimContext& ctx, Arena& arena) {
  for (size_t i = 0; i < production->ports.size(); ++i) {
    const auto& port = production->ports[i];
    uint32_t w = EvalTypeWidth(port.data_type);
    Logic4Vec val;
    if (i < actuals.size()) {
      val = actuals[i];
    } else if (port.default_value != nullptr) {
      val = EvalExpr(port.default_value, ctx, arena, w);
    } else {
      val = MakeLogic4VecVal(arena, w ? w : 32, 0);
    }
    uint32_t vw = val.width ? val.width : (w ? w : 32);
    auto* var = ctx.CreateLocalVariable(port.name, vw);
    var->value = val;
  }
}

static ExecTask ExecRsProduction(const Stmt* stmt, const RsProductionItem& call,
                                 SimContext& ctx, Arena& arena,
                                 RuleValueCapture* cap) {
  const auto* production = FindProduction(stmt, call.name);
  if (!production) co_return StmtResult::kDone;

  std::vector<Logic4Vec> actuals =
      EvalProductionActuals(production, call, ctx, arena);

  ctx.PushScope();
  BindProductionFormals(production, actuals, ctx, arena);

  // §18.17.7: returning data requires a (non-void) return type. Provide storage
  // for this production's return value and point the engine's return slot at
  // it, so a 'return <expr>' anywhere in the production writes here. Every
  // production is generated with a slot of its own, a void one with none: the
  // return statement assigns its expression to the production whose code block
  // holds it, so a void production left holding the slot of the production that
  // triggered it would write its own returned expression into that
  // production's value.
  Logic4Vec ret_value;
  bool returns_value = ProductionReturnsValue(production);
  if (returns_value) {
    uint32_t w = EvalTypeWidth(production->return_type);
    // §6.16: a string has no declared width and starts as "", the empty
    // string, of zero length. DispatchReturn hands this slot's width to
    // EvalExpr as the context width. A string literal ignores it, so
    // `return "minus"` keeps its five characters whatever the slot holds, but
    // a context-sized expression does not: a 32-bit slot sizes
    // `return k ? "minus" : "times"` to four characters through EvalTernary. A
    // zero width leaves every returned expression self-determined. Every other
    // return type EvalTypeWidth gives no width to keeps the 32-bit carrier.
    if (w == 0 && !ProductionReturnsString(production)) w = 32;
    ret_value = MakeLogic4VecVal(arena, w, 0);
  }
  Logic4Vec* prev_slot =
      ctx.SetRsReturnSlot(returns_value ? &ret_value : nullptr);

  const auto& selected = SelectRule(*production, ctx, arena);
  auto result = co_await ExecSelectedRule(stmt, selected, ctx, arena);

  ctx.SetRsReturnSlot(prev_slot);
  ctx.PopScope();

  // §6.16: a string cannot hold the "\0" character, and assigning a value to a
  // string drops that value's zero bytes. A returned string literal carries
  // none, but an integral expression returned by a string production carries
  // the zero bytes of its own width, so strip them before the value reaches
  // the implicit variable. Stripping a slot nothing returned into leaves the
  // empty string.
  if (returns_value && ProductionReturnsString(production)) {
    ret_value = StripStringZeros(ret_value, arena);
  }

  // §18.17.7: the implicit variable belongs to the rule that named the
  // production, so it is written once this production's own scope is gone.
  RuleProductionSlot slot = SlotForAppearance(cap, call, production->name);
  if (returns_value && slot.idx != 0) {
    StoreRuleProductionValue(slot, production, ret_value, ctx, arena);
  }

  // §18.17.6: a return aborts only the current production. Once that production
  // has finished generating, surface a normal completion so the enclosing rule
  // continues with the next production.
  if (result == StmtResult::kReturn) co_return StmtResult::kDone;
  co_return result;
}

ExecTask ExecRandsequence(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->rs_productions.empty()) co_return StmtResult::kDone;

  std::string_view top = stmt->rs_top_production;
  if (top.empty()) top = stmt->rs_productions[0].name;

  // 18.17: the randsequence statement creates an automatic scope enclosing the
  // generated productions and their code blocks. Production identifiers are
  // already resolved only within this statement, so the pushed scope provides
  // the enclosing automatic lifetime for the block.
  ctx.PushScope();
  RsProductionItem top_call;
  top_call.name = top;
  auto result = co_await ExecRsProduction(stmt, top_call, ctx, arena, nullptr);
  ctx.PopScope();

  (void)result;
  co_return StmtResult::kDone;
}

}  // namespace delta
