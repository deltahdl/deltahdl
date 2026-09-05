// §18.16's randcase and the §18.17 randsequence statement: ExecRandcase and
// ExecRandsequence, which src/simulator/stmt_exec.cpp reaches by name through
// simulator/stmt_exec_internal.h. ExecRandsequence pushes the automatic scope
// §18.17 gives the statement and generates its top production; SelectRule
// draws one rule of a production against the weights §18.17.1 attaches to the
// rules; ExecRsProd generates a production list in each of the forms
// §18.17.2's if-else, §18.17.3's case and §18.17.4's repeat give it;
// ExecRandJoinItems interleaves the operand sequences of §18.17.5's rand join;
// and ClassifyRandseqResult decides what the break and return of §18.17.6, and
// the disable of §9.6.2, do to the generation that is running.
//
// The values a production is called with and the values it returns stand in
// src/simulator/stmt_exec_randsequence_values.cpp, which answers §18.17.7 and
// is called from here alone.

#include <cmath>
#include <cstdint>
#include <string_view>
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
#include "simulator/stmt_exec_randsequence_internal.h"

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

// The two types below are also defined in
// src/simulator/stmt_exec_randsequence_values.cpp, which builds and reads them
// on behalf of the generation below. A change to either definition has to be
// made in both files.

static ExecTask ExecRsProduction(const Stmt* stmt, const RsProductionItem& call,
                                 SimContext& ctx, Arena& arena,
                                 RuleValueCapture* cap);

// §18.17.7: the implicit variables a rule declares for the value-returning
// productions it names, and the actual arguments a production is called with.
// Defined in src/simulator/stmt_exec_randsequence_values.cpp.
RuleValueCapture BuildRuleValueCapture(const Stmt* stmt, const RsRule& selected,
                                       SimContext& ctx);
RuleValueCapture BuildStepValueCapture(const Stmt* stmt,
                                       const std::vector<const RsProd*>& steps,
                                       SimContext& ctx);
RuleProductionSlot SlotForAppearance(const RuleValueCapture* cap,
                                     const RsProductionItem& call,
                                     std::string_view name);
void StoreRuleProductionValue(const RuleProductionSlot& slot,
                              const RsProduction* child,
                              const Logic4Vec& ret_value, SimContext& ctx,
                              Arena& arena);
std::vector<Logic4Vec> EvalProductionActuals(const RsProduction* production,
                                             const RsProductionItem& call,
                                             SimContext& ctx, Arena& arena);
void BindProductionFormals(const RsProduction* production,
                           const std::vector<Logic4Vec>& actuals,
                           SimContext& ctx, Arena& arena);

// §18.17.7: which production of the randsequence statement a name reaches,
// and whether it returns a value.
// src/simulator/stmt_exec_randsequence_values.cpp reads all three, so they
// carry external linkage.
const RsProduction* FindProduction(const Stmt* stmt, std::string_view name) {
  for (const auto& prod : stmt->rs_productions) {
    if (prod.name == name) return &prod;
  }
  return nullptr;
}

// §18.17.7: a production yields a readable value only when it declares a
// non-void return type. A production with no return type assumes a void return
// type, so it contributes no implicit variable.
bool ProductionReturnsValue(const RsProduction* p) {
  return p != nullptr && p->has_return_type &&
         p->return_type.kind != DataTypeKind::kVoid;
}

// §18.17.7: reports whether a production returns a string. §6.16 gives a
// string no declared width: it is as wide as the characters it holds, and one
// that was never written is "", the empty string, of zero length. Storage for
// such a value is therefore sized by what was returned, and not by the 32-bit
// carrier every other return type with no computable width falls back to.
bool ProductionReturnsString(const RsProduction* p) {
  return p != nullptr && p->has_return_type &&
         p->return_type.kind == DataTypeKind::kString;
}

// What a randsequence generation loop must do with the StmtResult its body
// left, factored out of the "unwind / abort the production / keep generating"
// branch every loop in this file repeats.
//
// kUnwind covers the two results that leave the whole generation. §18.17.6:
// "The break statement terminates the sequence generation", and §9.6.2: a
// disable "shall terminate the activity of a task or a named block", which is
// something the randsequence statement is running inside, so the generation
// ends either way and the loop hands the result to its caller unchanged.
// kAbortProduction covers return, which §18.17.6 gives a narrower reach: it
// "aborts the generation of the current production", and "sequence generation
// continues with the next production following the aborted production", so
// what a return ends is decided at the site rather than here. kKeepGenerating
// covers the rest.
enum class RandseqAction : uint8_t {
  kKeepGenerating,
  kAbortProduction,
  kUnwind,
};

static RandseqAction ClassifyRandseqResult(StmtResult result) {
  if (result == StmtResult::kBreak || result == StmtResult::kDisable) {
    return RandseqAction::kUnwind;
  }
  if (result == StmtResult::kReturn) return RandseqAction::kAbortProduction;
  return RandseqAction::kKeepGenerating;
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
  // §20.2: "The $finish system task causes the simulator to exit and pass
  // control back to the host operating system", so the iterations after the one
  // that ran it do not generate. SimContext::RequestFinish raises the stop the
  // process loops guard on, and this loop guards on it for the same reason.
  for (uint64_t i = 0; i < count && !ctx.StopRequested(); ++i) {
    auto result =
        co_await ExecRsProduction(stmt, prod.repeat_item, ctx, arena, cap);
    if (ClassifyRandseqResult(result) == RandseqAction::kUnwind) {
      co_return result;
    }
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
    if (ClassifyRandseqResult(result) != RandseqAction::kKeepGenerating) {
      block_result = result;
      break;
    }
    // §20.2: a $finish written here exits the simulator, so the statements
    // after it in this block do not run either. ExecBlock guards the statements
    // of a begin-end block on the same stop.
    if (ctx.StopRequested()) break;
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

// 18.17.5: run one operand rule's weight code in declaration order. A break or
// a disable must propagate out and end the whole interleaving (signalled via
// the returned StmtResult); a return only aborts this rule's contribution,
// leaving rule_aborted set so the caller emits no steps for it.
static ExecTask RunRandJoinRuleWeightCode(const RsRule& rule, SimContext& ctx,
                                          Arena& arena, bool& rule_aborted) {
  // §18.17 gives every code block within the randsequence an anonymous
  // automatic scope, and puts no condition on where the block stands, so an
  // operand production's trailing block gets one exactly as the block in
  // ExecSelectedRule does. The unwinding result is carried out of the loop
  // rather than returned from inside it, so the scope is popped however the
  // block ends.
  ctx.PushScope();
  StmtResult unwind = StmtResult::kDone;
  for (auto* s : rule.weight_code) {
    auto r = co_await ExecStmt(s, ctx, arena);
    auto action = ClassifyRandseqResult(r);
    if (action == RandseqAction::kUnwind) {
      unwind = r;
      break;
    }
    if (action == RandseqAction::kAbortProduction) {
      rule_aborted = true;
      break;
    }
    // §20.2: a $finish here exits the simulator, so the rest of this weight
    // code does not run.
    if (ctx.StopRequested()) break;
  }
  ctx.PopScope();
  co_return unwind;
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
  if (ClassifyRandseqResult(r) == RandseqAction::kUnwind) co_return r;
  if (rule_aborted) co_return StmtResult::kDone;
  CollectRandJoinSteps(rule, eng.arena, seq.steps);
  seq.cap = BuildStepValueCapture(eng.stmt, seq.steps, eng.ctx);
  co_return StmtResult::kDone;
}

// 18.17.5: expand each rand join operand one level into the production items of
// its selected rule, running that rule's weight code in declaration order
// first. A rule whose weight code breaks or is disabled ends the whole
// interleaving; one that returns contributes no steps. Sets aborted, and
// returns the result the caller must propagate, when the expansion must not
// finish.
static ExecTask BuildRandJoinSeqs(const RandseqEngine& eng,
                                  const RsRule& selected,
                                  std::vector<RandJoinSeq>& seqs,
                                  bool& aborted) {
  seqs.reserve(selected.rand_join_items.size());
  for (const auto& item : selected.rand_join_items) {
    RandJoinSeq seq;
    auto r = co_await BuildOneRandJoinSeq(eng, item, seq);
    if (ClassifyRandseqResult(r) == RandseqAction::kUnwind) {
      aborted = true;
      co_return r;
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

  // §20.2: a $finish executed by any operand exits the simulator, so the steps
  // the other operands have not contributed yet do not generate. The interleave
  // guards on the stop SimContext::RequestFinish raises, as the process loops
  // do.
  double exponent = 4.0 * bias - 1.0;
  while (!ctx.StopRequested()) {
    size_t chosen = ChooseRandJoinOperand(seqs, exponent, ctx);
    if (chosen == seqs.size()) break;

    auto result = co_await ExecOneRandJoinStep(eng, seqs[chosen]);
    auto action = ClassifyRandseqResult(result);
    if (action == RandseqAction::kUnwind) co_return result;
    if (action == RandseqAction::kAbortProduction) {
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

static ExecTask ExecRuleProds(const Stmt* stmt, const RsRule& selected,
                              SimContext& ctx, Arena& arena) {
  // §18.17.7: only the return values of productions already generated (to the
  // left of a code block) are available. Each generation stores its value into
  // the implicit variable as it finishes, so a later code block observes it
  // while an earlier one does not.
  RuleValueCapture cap = BuildRuleValueCapture(stmt, selected, ctx);
  for (const auto& prod : selected.prods) {
    auto result = co_await ExecRsProd(stmt, prod, ctx, arena, &cap);
    // §18.17.6: a return aborts the generation of the current production, so
    // the productions written after this one are not generated. Surface the
    // abort rather than reporting a normal completion, because the rule's own
    // code block is not generated either; ExecRsProduction turns it back into a
    // normal completion once the aborted production has finished. A break and a
    // disable are surfaced unchanged, each ending more than this rule.
    if (ClassifyRandseqResult(result) != RandseqAction::kKeepGenerating) {
      co_return result;
    }
    // §20.2: a $finish executed while this production generated exits the
    // simulator, so the productions after it in the list do not generate.
    if (ctx.StopRequested()) break;
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
  // §18.17: "each code block within the randsequence block creates an
  // anonymous automatic scope", and Syntax 18-14 makes this one of them --
  // `rs_rule ::= rs_production_list [ := rs_weight_specification [
  // rs_code_block ] ]`. It ran in the enclosing production's scope instead, so
  // a data declaration A.6.12 admits at the head of an rs_code_block outlived
  // the block: visible to the rest of the production, and still standing when
  // the same rule was selected again. ExecRsProdCodeBlock above pushes the
  // scope for the block written as a production of its own.
  //
  // The result is carried out of the loop rather than returned from inside it,
  // because a break, a return or a disable leaves the block early and a scope
  // left on the stack is worse than one never pushed.
  ctx.PushScope();
  StmtResult block_result = StmtResult::kDone;
  for (auto* s : selected.weight_code) {
    auto result = co_await ExecStmt(s, ctx, arena);
    if (ClassifyRandseqResult(result) != RandseqAction::kKeepGenerating) {
      block_result = result;
      break;
    }
    // §20.2: a $finish here exits the simulator, so the rest of this code block
    // does not run.
    if (ctx.StopRequested()) break;
  }
  ctx.PopScope();
  co_return block_result;
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

  // §18.17.6: "The break statement terminates the sequence generation. When a
  // break statement is executed from within a production code block, it forces
  // a jump out of the randsequence block", and the clause's own example
  // continues "on the line labeled next_statement". The randsequence statement
  // therefore absorbs a break and completes normally, and it absorbs nothing
  // else. §9.6.2 gives a disable a target outside this statement -- it "shall
  // terminate the activity of a task or a named block", and "execution shall
  // resume at the statement following the block or following the task-enabling
  // statement" -- so a disable raised in a production code block travels on to
  // whichever block or task it named. ExecRsProduction has already absorbed the
  // return of the top production, which §18.17.6 gives no reach past the
  // production it aborts.
  if (result == StmtResult::kBreak) co_return StmtResult::kDone;
  co_return result;
}

}  // namespace delta
