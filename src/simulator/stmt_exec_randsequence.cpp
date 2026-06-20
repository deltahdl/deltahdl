#include <cmath>
#include <cstdint>
#include <cstring>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
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
                          "randcase: all weights are zero; no branch selected");
    co_return StmtResult::kDone;
  }

  // §18.16: one random number in [0, sum); branches are selected in
  // declaration order, with smaller numbers landing on the earlier (top)
  // weights. A zero-weight branch leaves the cumulative total unchanged and so
  // can never be selected. A sum wider than 32 bits cannot be covered by a
  // single 32-bit draw, so compose the random number from more than one draw
  // to reach the full [0, sum) range.
  uint64_t pick;
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

static ExecTask ExecRsProduction(const Stmt* stmt, const RsProductionItem& call,
                                 SimContext& ctx, Arena& arena,
                                 Logic4Vec* out_value);

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

static ExecTask ExecRsProd(const Stmt* stmt, const RsProd& prod,
                           SimContext& ctx, Arena& arena, Logic4Vec* out_value);

static ExecTask ExecRsProdIf(const Stmt* stmt, const RsProd& prod,
                             SimContext& ctx, Arena& arena,
                             Logic4Vec* out_value) {
  if (EvalExpr(prod.condition, ctx, arena).ToUint64() != 0) {
    co_return co_await ExecRsProduction(stmt, prod.if_true, ctx, arena,
                                        out_value);
  }
  if (prod.has_else) {
    co_return co_await ExecRsProduction(stmt, prod.if_false, ctx, arena,
                                        out_value);
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecRsProdRepeat(const Stmt* stmt, const RsProd& prod,
                                 SimContext& ctx, Arena& arena,
                                 Logic4Vec* out_value) {
  auto count = EvalExpr(prod.repeat_count, ctx, arena).ToUint64();
  for (uint64_t i = 0; i < count; ++i) {
    auto result = co_await ExecRsProduction(stmt, prod.repeat_item, ctx, arena,
                                            out_value);
    if (result == StmtResult::kBreak) co_return StmtResult::kBreak;
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecRsProdCase(const Stmt* stmt, const RsProd& prod,
                               SimContext& ctx, Arena& arena,
                               Logic4Vec* out_value) {
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
        co_return co_await ExecRsProduction(stmt, ci.item, ctx, arena,
                                            out_value);
      }
    }
  }
  if (default_item) {
    co_return co_await ExecRsProduction(stmt, default_item->item, ctx, arena,
                                        out_value);
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecRsProd(const Stmt* stmt, const RsProd& prod,
                           SimContext& ctx, Arena& arena,
                           Logic4Vec* out_value) {
  switch (prod.kind) {
    case RsProdKind::kCodeBlock: {
      // 18.17: every code block inside a randsequence is its own anonymous
      // automatic scope. Variables it declares are recreated on each execution
      // and do not leak to sibling code blocks or outlive the block, so we
      // bracket the statements with a fresh automatic scope.
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
    case RsProdKind::kItem:
      co_return co_await ExecRsProduction(stmt, prod.item, ctx, arena,
                                          out_value);
    case RsProdKind::kIf:
      co_return co_await ExecRsProdIf(stmt, prod, ctx, arena, out_value);
    case RsProdKind::kRepeat:
      co_return co_await ExecRsProdRepeat(stmt, prod, ctx, arena, out_value);
    case RsProdKind::kCase:
      co_return co_await ExecRsProdCase(stmt, prod, ctx, arena, out_value);
  }
  co_return StmtResult::kDone;
}

static const RsRule& SelectRule(const RsProduction& production, SimContext& ctx,
                                Arena& arena) {
  if (production.rules.size() <= 1) return production.rules[0];
  uint64_t total_weight = 0;
  for (const auto& rule : production.rules) {
    total_weight +=
        rule.weight ? EvalExpr(rule.weight, ctx, arena).ToUint64() : 1;
  }
  if (total_weight == 0) return production.rules[0];
  uint64_t pick = ctx.Urandom32() % total_weight;
  uint64_t cumulative = 0;
  for (const auto& rule : production.rules) {
    cumulative +=
        rule.weight ? EvalExpr(rule.weight, ctx, arena).ToUint64() : 1;
    if (pick < cumulative) return rule;
  }
  return production.rules[0];
}

// 18.17.5: the optional weight following the rand join keywords states, as a
// real value, how strongly the remaining length of each operand sequence biases
// which sequence advances next. The standard constrains it to [0.0, 1.0], so
// clamp any out of range value to that interval, and use the neutral 0.5 when
// the expression is omitted.
static double EvalRandJoinBias(Expr* expr, SimContext& ctx, Arena& arena) {
  if (!expr) return 0.5;
  auto v = EvalExpr(expr, ctx, arena);
  double f;
  if (v.is_real) {
    if (v.width == 32) {
      float ff = 0.0f;
      auto bits = static_cast<uint32_t>(v.ToUint64());
      std::memcpy(&ff, &bits, sizeof(float));
      f = static_cast<double>(ff);
    } else {
      uint64_t bits = v.ToUint64();
      std::memcpy(&f, &bits, sizeof(double));
    }
  } else {
    f = static_cast<double>(v.ToUint64());
  }
  if (f < 0.0) f = 0.0;
  if (f > 1.0) f = 1.0;
  return f;
}

// One operand of a rand join, expanded one level (to depth 1) into the
// production items it will contribute. The interleaver emits these items in
// order; cursor marks how many have already been generated.
struct RandJoinSeq {
  std::vector<const RsProd*> steps;
  size_t cursor = 0;
  size_t Remaining() const { return steps.size() - cursor; }
};

// 18.17.5: expanding an operand to depth 1 yields the production items of its
// selected rule. A nested rand join contributes its own operands as the
// depth-1 items, so wrap each in a production item step.
static void CollectRandJoinSteps(const RsRule& rule, Arena& arena,
                                 std::vector<const RsProd*>& steps) {
  if (rule.is_rand_join) {
    for (const auto& item : rule.rand_join_items) {
      auto* p = arena.New<RsProd>();
      p->kind = RsProdKind::kItem;
      p->item = item;
      steps.push_back(p);
    }
    return;
  }
  for (const auto& prod : rule.prods) steps.push_back(&prod);
}

static ExecTask ExecRandJoinItems(const Stmt* stmt, const RsRule& selected,
                                  SimContext& ctx, Arena& arena) {
  // 18.17.5: rand join randomly interleaves its operand sequences while keeping
  // the productions within each operand in their original relative order. Each
  // operand is first expanded one level (depth 1) into the production items of
  // its selected rule; those items are the units that get interleaved.
  double bias = EvalRandJoinBias(selected.rand_join_expr, ctx, arena);

  std::vector<RandJoinSeq> seqs;
  seqs.reserve(selected.rand_join_items.size());
  for (const auto& item : selected.rand_join_items) {
    const auto* production = FindProduction(stmt, item.name);
    RandJoinSeq seq;
    if (production) {
      const auto& rule = SelectRule(*production, ctx, arena);
      bool aborted = false;
      for (auto* s : rule.weight_code) {
        auto r = co_await ExecStmt(s, ctx, arena);
        if (r == StmtResult::kBreak) co_return StmtResult::kBreak;
        if (r == StmtResult::kReturn) {
          aborted = true;
          break;
        }
      }
      if (!aborted) CollectRandJoinSteps(rule, arena, seq.steps);
    }
    seqs.push_back(std::move(seq));
  }

  // 18.17.5: at each step choose one operand and emit its next production. A
  // sequence's length is the number of productions it has not yet contributed.
  // The bias maps to an exponent on that length: 0.5 (exponent 1) keeps the
  // choice proportional to remaining length so no length is prioritized, values
  // toward 0.0 (negative exponent) favor the shortest remaining sequences, and
  // values toward 1.0 favor the longest.
  double exponent = 4.0 * bias - 1.0;
  for (;;) {
    double total = 0.0;
    for (const auto& seq : seqs) {
      if (seq.Remaining() > 0)
        total += std::pow(static_cast<double>(seq.Remaining()), exponent);
    }
    if (total <= 0.0) break;  // every operand sequence has been drained

    double draw = (ctx.Urandom32() / 4294967296.0) * total;
    double cumulative = 0.0;
    size_t chosen = seqs.size();
    for (size_t i = 0; i < seqs.size(); ++i) {
      if (seqs[i].Remaining() == 0) continue;
      cumulative +=
          std::pow(static_cast<double>(seqs[i].Remaining()), exponent);
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

    const RsProd* step = seqs[chosen].steps[seqs[chosen].cursor++];
    auto result = co_await ExecRsProd(stmt, *step, ctx, arena, nullptr);
    if (result == StmtResult::kBreak) co_return StmtResult::kBreak;
    if (result == StmtResult::kReturn) {
      // 18.17.6: return aborts the current production; drop the remainder of
      // this operand's sequence and keep interleaving the others.
      seqs[chosen].cursor = seqs[chosen].steps.size();
    }
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecRuleProds(const Stmt* stmt, const RsRule& selected,
                              SimContext& ctx, Arena& arena) {
  // §18.17.7: within a rule, a variable is implicitly declared for each
  // value-returning production that appears. A production appearing once yields
  // a scalar named after the production; a production appearing more than once
  // yields an array indexed 1..N, with element i holding the value returned by
  // the i-th appearance in syntactic order. Pre-scan the rule's production
  // items to count each name's appearances so a multiply appearing
  // value-returning production can be registered as an array before any code
  // block reads it.
  std::unordered_map<std::string_view, int> total_count;
  for (const auto& prod : selected.prods) {
    if (prod.kind != RsProdKind::kItem) continue;
    if (ProductionReturnsValue(FindProduction(stmt, prod.item.name)))
      total_count[prod.item.name]++;
  }
  for (const auto& [name, n] : total_count) {
    if (n <= 1) continue;
    const auto* child = FindProduction(stmt, name);
    ArrayInfo info;
    info.lo = 1;
    info.size = static_cast<uint32_t>(n);
    uint32_t w = EvalTypeWidth(child->return_type);
    info.elem_width = w ? w : 32;
    ctx.RegisterArray(name, info);
  }

  // §18.17.7: only the return values of productions already generated (to the
  // left of a code block) are available. Each generation stores its value into
  // the implicit variable immediately, so later code blocks observe it while
  // earlier ones do not.
  std::unordered_map<std::string_view, int> seen_count;
  for (const auto& prod : selected.prods) {
    Logic4Vec ret_value;
    const RsProduction* child = nullptr;
    Logic4Vec* slot = nullptr;
    if (prod.kind == RsProdKind::kItem) {
      child = FindProduction(stmt, prod.item.name);
      if (ProductionReturnsValue(child)) slot = &ret_value;
    }

    auto result = co_await ExecRsProd(stmt, prod, ctx, arena, slot);

    if (slot != nullptr) {
      uint32_t w = EvalTypeWidth(child->return_type);
      if (w == 0) w = ret_value.width ? ret_value.width : 32;
      int idx = ++seen_count[prod.item.name];
      Variable* var;
      if (total_count[prod.item.name] > 1) {
        // Indexed element names are built at run time, so intern the name in
        // the arena: the scope map keys on the string_view and needs stable
        // storage.
        auto name =
            std::string(prod.item.name) + "[" + std::to_string(idx) + "]";
        var = ctx.CreateLocalVariable(
            *arena.Create<std::string>(std::move(name)), w);
      } else {
        var = ctx.CreateLocalVariable(prod.item.name, w);
      }
      var->value = ret_value;
    }

    if (result == StmtResult::kBreak) co_return StmtResult::kBreak;
    if (result == StmtResult::kReturn) co_return StmtResult::kDone;
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecSelectedRule(const Stmt* stmt, const RsRule& selected,
                                 SimContext& ctx, Arena& arena) {
  for (auto* s : selected.weight_code) {
    auto result = co_await ExecStmt(s, ctx, arena);
    if (result == StmtResult::kBreak || result == StmtResult::kReturn) {
      co_return result;
    }
  }
  if (selected.is_rand_join) {
    co_return co_await ExecRandJoinItems(stmt, selected, ctx, arena);
  }
  co_return co_await ExecRuleProds(stmt, selected, ctx, arena);
}

static ExecTask ExecRsProduction(const Stmt* stmt, const RsProductionItem& call,
                                 SimContext& ctx, Arena& arena,
                                 Logic4Vec* out_value) {
  const auto* production = FindProduction(stmt, call.name);
  if (!production) co_return StmtResult::kDone;

  // §18.17.7: passing data to a production uses the same syntax as a task call.
  // Evaluate the actual arguments in the caller's scope, before the
  // production's own scope is entered, sizing each to its formal's declared
  // width.
  std::vector<Logic4Vec> actuals;
  actuals.reserve(call.args.size());
  for (size_t i = 0; i < call.args.size(); ++i) {
    uint32_t w = i < production->ports.size()
                     ? EvalTypeWidth(production->ports[i].data_type)
                     : 0;
    actuals.push_back(EvalExpr(call.args[i], ctx, arena, w));
  }

  // §18.17.7: a production creates a scope that encompasses all its rules and
  // code blocks; formal arguments bound here are therefore available throughout
  // the production. Bind each formal by position, falling back to its default
  // value, then to zero, when no actual is supplied.
  ctx.PushScope();
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

  // §18.17.7: returning data requires a (non-void) return type. Provide storage
  // for this production's return value and point the engine's return slot at it
  // so a 'return <expr>' anywhere in the production writes here, saving and
  // restoring any enclosing production's slot for correct nesting.
  Logic4Vec ret_value;
  bool returns_value = ProductionReturnsValue(production);
  Logic4Vec* prev_slot = nullptr;
  if (returns_value) {
    uint32_t w = EvalTypeWidth(production->return_type);
    if (w == 0) w = 32;
    ret_value = MakeLogic4VecVal(arena, w, 0);
    prev_slot = ctx.SetRsReturnSlot(&ret_value);
  }

  const auto& selected = SelectRule(*production, ctx, arena);
  auto result = co_await ExecSelectedRule(stmt, selected, ctx, arena);

  if (returns_value) ctx.SetRsReturnSlot(prev_slot);
  ctx.PopScope();

  if (out_value != nullptr && returns_value) *out_value = ret_value;

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
