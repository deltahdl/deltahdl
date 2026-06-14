#include "simulator/stmt_exec.h"

#include <cmath>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/awaiters.h"
#include "simulator/evaluation.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"

namespace delta {

static ExecTask ExecRandcase(const Stmt* stmt, SimContext& ctx, Arena& arena) {
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
    auto result =
        co_await ExecRsProduction(stmt, prod.repeat_item, ctx, arena, out_value);
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
        // Indexed element names are built at run time, so intern the name in the
        // arena: the scope map keys on the string_view and needs stable storage.
        auto name = std::string(prod.item.name) + "[" + std::to_string(idx) +
                    "]";
        var = ctx.CreateLocalVariable(*arena.Create<std::string>(std::move(name)),
                                      w);
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
  // Evaluate the actual arguments in the caller's scope, before the production's
  // own scope is entered, sizing each to its formal's declared width.
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

static ExecTask ExecRandsequence(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena) {
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

static ExecTask ExecBlock(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool named = !stmt->label.empty();
  if (named) {
    ctx.PushStaticScope(stmt->label);
    ctx.RegisterNamedScope(stmt->label, ctx.CurrentProcess());
    ctx.PushActiveNamedScope(stmt->label);
  }
  for (auto* s : stmt->stmts) {
    auto result = co_await ExecStmt(s, ctx, arena);
    if (result == StmtResult::kDisable) {
      if (named && ctx.GetDisableTarget() == stmt->label) {
        ctx.ClearDisableTarget();
        ctx.PopActiveNamedScope();
        ctx.UnregisterNamedScope(stmt->label, ctx.CurrentProcess());
        ctx.PopStaticScope(stmt->label);
        co_return StmtResult::kDone;
      }
      if (named) {
        ctx.PopActiveNamedScope();
        ctx.UnregisterNamedScope(stmt->label, ctx.CurrentProcess());
        ctx.PopStaticScope(stmt->label);
      }
      co_return StmtResult::kDisable;
    }
    if (result != StmtResult::kDone) {
      if (named) {
        ctx.PopActiveNamedScope();
        ctx.UnregisterNamedScope(stmt->label, ctx.CurrentProcess());
        ctx.PopStaticScope(stmt->label);
      }
      co_return result;
    }
    if (ctx.StopRequested()) {
      if (named) {
        ctx.PopActiveNamedScope();
        ctx.UnregisterNamedScope(stmt->label, ctx.CurrentProcess());
        ctx.PopStaticScope(stmt->label);
      }
      co_return StmtResult::kDone;
    }

    if (auto* cur = ctx.CurrentProcess(); cur && !cur->active) {
      if (named) {
        ctx.PopActiveNamedScope();
        ctx.UnregisterNamedScope(stmt->label, ctx.CurrentProcess());
        ctx.PopStaticScope(stmt->label);
      }
      co_return StmtResult::kDone;
    }
  }
  if (named) {
    ctx.PopActiveNamedScope();
    ctx.UnregisterNamedScope(stmt->label, ctx.CurrentProcess());
    ctx.PopStaticScope(stmt->label);
  }
  co_return StmtResult::kDone;
}

struct UniqueIfResult {
  const Stmt* first_match = nullptr;
  int match_count = 0;
  bool has_final_else = false;
};

static UniqueIfResult EvalUniqueIfChain(const Stmt* stmt, SimContext& ctx,
                                        Arena& arena) {
  UniqueIfResult result;
  for (const Stmt* cur = stmt; cur && cur->kind == StmtKind::kIf;
       cur = cur->else_branch) {
    auto cond = EvalExpr(cur->condition, ctx, arena);
    if (cond.IsTruthy()) {
      result.match_count++;
      if (!result.first_match) result.first_match = cur;
    }
    if (cur->else_branch && cur->else_branch->kind != StmtKind::kIf) {
      result.has_final_else = true;
    }
  }
  return result;
}

static const Stmt* FindFinalElse(const Stmt* stmt) {
  const Stmt* cur = stmt;
  while (cur->else_branch && cur->else_branch->kind == StmtKind::kIf) {
    cur = cur->else_branch;
  }
  return cur->else_branch;
}

static ExecTask ExecUniqueIf(const Stmt* stmt, CaseQualifier qual,
                             SimContext& ctx, Arena& arena) {
  auto info = EvalUniqueIfChain(stmt, ctx, arena);

  if (info.match_count > 1) {
    ctx.AddPendingViolation("unique if: multiple conditions matched");
  }
  if (info.first_match) {
    co_return co_await ExecStmt(info.first_match->then_branch, ctx, arena);
  }
  if (info.has_final_else) {
    const Stmt* final_else = FindFinalElse(stmt);
    if (final_else) co_return co_await ExecStmt(final_else, ctx, arena);
  }
  if (!info.has_final_else && qual == CaseQualifier::kUnique) {
    ctx.AddPendingViolation("unique if: no condition matched");
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecPriorityIf(const Stmt* stmt, SimContext& ctx,
                               Arena& arena) {
  bool has_final_else = false;
  for (const Stmt* cur = stmt; cur && cur->kind == StmtKind::kIf;
       cur = cur->else_branch) {
    auto cond = EvalExpr(cur->condition, ctx, arena);
    if (cond.IsTruthy()) {
      co_return co_await ExecStmt(cur->then_branch, ctx, arena);
    }
    if (cur->else_branch && cur->else_branch->kind != StmtKind::kIf) {
      has_final_else = true;
    }
  }
  if (has_final_else) {
    const Stmt* final_else = FindFinalElse(stmt);
    if (final_else) co_return co_await ExecStmt(final_else, ctx, arena);
  }
  if (!has_final_else) {
    ctx.AddPendingViolation("priority if: no condition matched");
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecIf(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  auto qual = stmt->qualifier;

  if (qual == CaseQualifier::kUnique || qual == CaseQualifier::kUnique0) {
    auto r = co_await ExecUniqueIf(stmt, qual, ctx, arena);
    if (labeled) ctx.PopStaticScope(stmt->label);
    co_return r;
  }
  if (qual == CaseQualifier::kPriority) {
    auto r = co_await ExecPriorityIf(stmt, ctx, arena);
    if (labeled) ctx.PopStaticScope(stmt->label);
    co_return r;
  }

  auto cond = EvalExpr(stmt->condition, ctx, arena);
  if (cond.IsTruthy()) {
    auto r = co_await ExecStmt(stmt->then_branch, ctx, arena);
    if (labeled) ctx.PopStaticScope(stmt->label);
    co_return r;
  }
  if (stmt->else_branch) {
    auto r = co_await ExecStmt(stmt->else_branch, ctx, arena);
    if (labeled) ctx.PopStaticScope(stmt->label);
    co_return r;
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

static bool BitIsZ(const Logic4Vec& v, uint32_t bit) {
  if (v.nwords == 0 || !v.words) return false;
  uint32_t wi = bit / 64;
  uint32_t bi = bit % 64;
  if (wi >= v.nwords) return false;
  bool a = (v.words[wi].aval >> bi) & 1;
  bool b = (v.words[wi].bval >> bi) & 1;
  return a && b;
}

static bool BitIsXZ(const Logic4Vec& v, uint32_t bit) {
  if (v.nwords == 0 || !v.words) return false;
  uint32_t wi = bit / 64;
  uint32_t bi = bit % 64;
  if (wi >= v.nwords) return false;
  return (v.words[wi].bval >> bi) & 1;
}

using BitPredicate = bool (*)(const Logic4Vec&, uint32_t);

static bool CaseDontCareMatch(const Logic4Vec& sel, const Logic4Vec& pat,
                              BitPredicate skip_bit) {
  uint32_t width = (sel.width > pat.width) ? sel.width : pat.width;
  for (uint32_t i = 0; i < width; ++i) {
    if (skip_bit(sel, i) || skip_bit(pat, i)) continue;
    uint32_t swi = i / 64, sbi = i % 64;
    uint32_t pwi = i / 64, pbi = i % 64;
    bool sa = (swi < sel.nwords) && ((sel.words[swi].aval >> sbi) & 1);
    bool pa = (pwi < pat.nwords) && ((pat.words[pwi].aval >> pbi) & 1);
    if (sa != pa) return false;
  }
  return true;
}

static bool CasexMatch(const Logic4Vec& sel, const Logic4Vec& pat) {
  return CaseDontCareMatch(sel, pat, BitIsXZ);
}

static bool CasezMatch(const Logic4Vec& sel, const Logic4Vec& pat) {
  return CaseDontCareMatch(sel, pat, BitIsZ);
}

static bool CaseInsideValueMatch(const Logic4Vec& sel, const Logic4Vec& pat) {
  if (!sel.IsKnown()) return false;
  uint32_t nw = (sel.nwords > pat.nwords) ? sel.nwords : pat.nwords;
  for (uint32_t i = 0; i < nw; ++i) {
    uint64_t sa = (i < sel.nwords) ? sel.words[i].aval : 0;
    uint64_t pa = (i < pat.nwords) ? pat.words[i].aval : 0;
    uint64_t pb = (i < pat.nwords) ? pat.words[i].bval : 0;

    if ((sa ^ pa) & ~pb) return false;
  }
  return true;
}

static bool CaseInsideRangeMatch(const Logic4Vec& sel, const Expr* pat,
                                 SimContext& ctx, Arena& arena) {
  if (!sel.IsKnown()) return false;
  uint64_t sv = sel.ToUint64();

  if (pat->op == TokenKind::kPlusSlashMinus ||
      pat->op == TokenKind::kPlusPercentMinus) {
    auto a_v = EvalExpr(pat->index, ctx, arena);
    auto b_v = EvalExpr(pat->index_end, ctx, arena);
    if (!a_v.IsKnown() || !b_v.IsKnown()) return false;
    uint64_t a = a_v.ToUint64();
    uint64_t b = b_v.ToUint64();
    uint64_t tol = b;
    if (pat->op == TokenKind::kPlusPercentMinus) tol = a * b / 100;
    uint64_t lo = (a >= tol) ? a - tol : 0;
    uint64_t hi = a + tol;
    if (lo > hi) { uint64_t t = lo; lo = hi; hi = t; }
    return sv >= lo && sv <= hi;
  }

  auto is_dollar = [](const Expr* e) {
    return e->kind == ExprKind::kIdentifier && e->text == "$";
  };
  uint64_t lo = is_dollar(pat->index)
                    ? 0
                    : EvalExpr(pat->index, ctx, arena).ToUint64();
  uint64_t hi = is_dollar(pat->index_end)
                    ? ((sel.width >= 64) ? ~uint64_t{0}
                                         : (uint64_t{1} << sel.width) - 1)
                    : EvalExpr(pat->index_end, ctx, arena).ToUint64();
  if (lo > hi) { uint64_t t = lo; lo = hi; hi = t; }
  return sv >= lo && sv <= hi;
}

static bool CaseInsidePatternMatch(const Logic4Vec& sel, const Expr* pat,
                                   SimContext& ctx, Arena& arena) {
  if (pat->kind == ExprKind::kSelect && pat->index && pat->index_end)
    return CaseInsideRangeMatch(sel, pat, ctx, arena);
  auto pat_val = EvalExpr(pat, ctx, arena);
  return CaseInsideValueMatch(sel, pat_val);
}

static bool CaseExactMatch(const Logic4Vec& sel, const Logic4Vec& pat) {
  uint32_t nw = (sel.nwords > pat.nwords) ? sel.nwords : pat.nwords;
  for (uint32_t i = 0; i < nw; ++i) {
    uint64_t sa = (i < sel.nwords) ? sel.words[i].aval : 0;
    uint64_t sb = (i < sel.nwords) ? sel.words[i].bval : 0;
    uint64_t pa = (i < pat.nwords) ? pat.words[i].aval : 0;
    uint64_t pb = (i < pat.nwords) ? pat.words[i].bval : 0;
    if (sa != pa || sb != pb) return false;
  }
  return true;
}

static bool CaseMatchesMatch(const Logic4Vec& sel, const Logic4Vec& pat,
                             TokenKind case_kind) {
  if (case_kind == TokenKind::kKwCasex) return CasexMatch(sel, pat);
  if (case_kind == TokenKind::kKwCasez) return CasezMatch(sel, pat);
  return CaseInsideValueMatch(sel, pat);
}

static bool CaseMatchesPatternMatch(const Logic4Vec& sel, const Expr* pat_expr,
                                    SimContext& ctx, Arena& arena,
                                    TokenKind case_kind) {

  if (pat_expr->kind == ExprKind::kBinary &&
      pat_expr->op == TokenKind::kAmpAmpAmp) {
    auto pat_val = EvalExpr(pat_expr->lhs, ctx, arena);
    if (!CaseMatchesMatch(sel, pat_val, case_kind)) return false;
    auto guard = EvalExpr(pat_expr->rhs, ctx, arena);
    return guard.IsTruthy();
  }
  auto pv = EvalExpr(pat_expr, ctx, arena);
  return CaseMatchesMatch(sel, pv, case_kind);
}

static bool CaseItemMatches(const Logic4Vec& sel, const Logic4Vec& pat,
                            TokenKind case_kind) {
  if (case_kind == TokenKind::kKwCasex) return CasexMatch(sel, pat);
  if (case_kind == TokenKind::kKwCasez) return CasezMatch(sel, pat);
  return CaseExactMatch(sel, pat);
}

static bool CasePatternMatch(const Logic4Vec& sel, const Expr* pat,
                             const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->case_inside) return CaseInsidePatternMatch(sel, pat, ctx, arena);
  if (stmt->case_matches)
    return CaseMatchesPatternMatch(sel, pat, ctx, arena, stmt->case_kind);
  return CaseItemMatches(sel, EvalExpr(pat, ctx, arena), stmt->case_kind);
}

static bool CaseItemHasMatch(const Logic4Vec& sel, const CaseItem& item,
                             const Stmt* stmt, SimContext& ctx, Arena& arena) {
  for (auto* pat : item.patterns) {
    if (CasePatternMatch(sel, pat, stmt, ctx, arena)) return true;
  }
  return false;
}

static const Stmt* FindCaseDefault(const Stmt* stmt) {
  for (const auto& item : stmt->case_items) {
    if (item.is_default) return item.body;
  }
  return nullptr;
}

struct UniqueCaseResult {
  const Stmt* first_match_body = nullptr;
  int match_count = 0;
  bool has_default = false;
};

static UniqueCaseResult ScanUniqueCaseItems(const Logic4Vec& sel,
                                            const Stmt* stmt, SimContext& ctx,
                                            Arena& arena) {
  UniqueCaseResult result;
  for (const auto& item : stmt->case_items) {
    if (item.is_default) {
      result.has_default = true;
      continue;
    }
    if (CaseItemHasMatch(sel, item, stmt, ctx, arena)) {
      result.match_count++;
      if (!result.first_match_body) result.first_match_body = item.body;
    }
  }
  return result;
}

static ExecTask ExecUniqueCase(const Stmt* stmt, const Logic4Vec& sel,
                               CaseQualifier qual, SimContext& ctx,
                               Arena& arena) {
  auto info = ScanUniqueCaseItems(sel, stmt, ctx, arena);

  if (info.match_count > 1) {
    ctx.AddPendingViolation("unique case: multiple items matched");
  }
  if (info.first_match_body) {
    co_return co_await ExecStmt(info.first_match_body, ctx, arena);
  }
  auto* default_body = FindCaseDefault(stmt);
  if (default_body) co_return co_await ExecStmt(default_body, ctx, arena);
  if (!info.has_default && qual == CaseQualifier::kUnique) {
    ctx.AddPendingViolation("unique case: no matching item found");
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecStandardCase(const Stmt* stmt, const Logic4Vec& sel,
                                 CaseQualifier qual, SimContext& ctx,
                                 Arena& arena) {
  for (const auto& item : stmt->case_items) {
    if (item.is_default) continue;
    if (CaseItemHasMatch(sel, item, stmt, ctx, arena)) {
      co_return co_await ExecStmt(item.body, ctx, arena);
    }
  }
  auto* default_body = FindCaseDefault(stmt);
  if (default_body) co_return co_await ExecStmt(default_body, ctx, arena);
  if (qual == CaseQualifier::kPriority) {
    ctx.AddPendingViolation("priority case: no matching item found");
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecCase(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  auto qual = stmt->qualifier;
  auto sel = EvalExpr(stmt->condition, ctx, arena);

  StmtResult r;
  if (qual == CaseQualifier::kUnique || qual == CaseQualifier::kUnique0) {
    r = co_await ExecUniqueCase(stmt, sel, qual, ctx, arena);
  } else {
    r = co_await ExecStandardCase(stmt, sel, qual, ctx, arena);
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return r;
}

static void CreateForInitVars(const Stmt* stmt, SimContext& ctx) {
  for (size_t i = 0; i < stmt->for_inits.size(); ++i) {
    if (i >= stmt->for_init_types.size()) break;
    if (stmt->for_init_types[i].kind == DataTypeKind::kImplicit) continue;
    auto* init = stmt->for_inits[i];
    if (!init || !init->lhs) continue;
    uint32_t w = EvalTypeWidth(stmt->for_init_types[i]);
    if (w == 0) w = 32;
    ctx.CreateLocalVariable(init->lhs->text, w);
  }
}

static bool HasTypedForInit(const Stmt* stmt) {
  for (const auto& t : stmt->for_init_types) {
    if (t.kind != DataTypeKind::kImplicit) return true;
  }
  return false;
}

static ExecTask ExecFor(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  bool scoped = HasTypedForInit(stmt);
  if (scoped) ctx.PushScope();
  CreateForInitVars(stmt, ctx);
  for (auto* init : stmt->for_inits)
    co_await ExecStmt(init, ctx, arena);
  while (!ctx.StopRequested()) {
    if (stmt->for_cond) {
      auto cond = EvalExpr(stmt->for_cond, ctx, arena);
      if (!cond.IsTruthy()) break;
    }
    auto result = co_await ExecStmt(stmt->for_body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      if (scoped) ctx.PopScope();
      if (labeled) ctx.PopStaticScope(stmt->label);
      co_return result;
    }
    for (auto* step : stmt->for_steps)
      co_await ExecStmt(step, ctx, arena);
  }
  if (scoped) ctx.PopScope();
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

static ExecTask ExecWhile(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  while (!ctx.StopRequested()) {
    auto cond = EvalExpr(stmt->condition, ctx, arena);
    if (!cond.IsTruthy()) break;
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      if (labeled) ctx.PopStaticScope(stmt->label);
      co_return result;
    }
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

static ExecTask ExecForever(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  while (!ctx.StopRequested()) {
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      if (labeled) ctx.PopStaticScope(stmt->label);
      co_return result;
    }
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

// §12.7.2: derive how many times a repeat-loop body runs from the count
// expression, already evaluated once before the loop begins. An unknown or
// high-impedance value, or a negative value of a signed expression, yields no
// iterations.
static uint64_t RepeatIterationCount(const Logic4Vec& count_val) {
  if (!count_val.IsKnown()) return 0;
  if (count_val.is_signed && count_val.width > 0) {
    uint32_t msb_word = (count_val.width - 1) / 64;
    uint64_t msb_mask = uint64_t{1} << ((count_val.width - 1) % 64);
    if (count_val.words[msb_word].aval & msb_mask) return 0;
  }
  return count_val.ToUint64();
}

static ExecTask ExecRepeat(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  auto count_val = EvalExpr(stmt->condition, ctx, arena);
  uint64_t count = RepeatIterationCount(count_val);
  for (uint64_t i = 0; i < count && !ctx.StopRequested(); ++i) {
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      if (labeled) ctx.PopStaticScope(stmt->label);
      co_return result;
    }
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

static ExecTask ExecDoWhile(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  do {
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      if (labeled) ctx.PopStaticScope(stmt->label);
      co_return result;
    }
    auto cond = EvalExpr(stmt->condition, ctx, arena);
    if (!cond.IsTruthy()) break;
  } while (!ctx.StopRequested());
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

static std::string GetForeachArrayName(const Expr* expr) {
  if (!expr) return {};
  if (expr->kind == ExprKind::kIdentifier) return std::string(expr->text);
  if (expr->kind == ExprKind::kMemberAccess) {
    std::string name;
    BuildLhsName(expr, name);
    return name;
  }
  return {};
}

static uint32_t GetArraySize(const Stmt* stmt, SimContext& ctx) {
  std::string name = GetForeachArrayName(stmt->expr);
  if (name.empty()) return 0;
  auto* info = ctx.FindArrayInfo(name);
  if (info) return info->size;
  auto* var = ctx.FindVariable(name);
  if (!var) return 0;
  // §12.7.3: a string is treated as a dynamic array of bytes, so the loop runs
  // once per character. The value packs eight bits per character, so the
  // character count is the bit width divided by eight.
  if (ctx.IsStringVariable(name)) return var->value.width / 8;
  return var->value.width;
}

static ExecTask ExecForeach(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  std::string arr_name = GetForeachArrayName(stmt->expr);
  if (!arr_name.empty()) {
    auto* aa = ctx.FindAssocArray(arr_name);
    if (aa && aa->is_wildcard) {
      ctx.GetDiag().Error(
          {}, "foreach not allowed on wildcard associative array '" +
                  arr_name + "'");
      if (labeled) ctx.PopStaticScope(stmt->label);
      co_return StmtResult::kDone;
    }
  }
  uint32_t size = GetArraySize(stmt, ctx);
  if (size == 0) {
    if (labeled) ctx.PopStaticScope(stmt->label);
    co_return StmtResult::kDone;
  }

  std::string_view iter_name;
  if (!stmt->foreach_vars.empty() && !stmt->foreach_vars[0].empty()) {
    iter_name = stmt->foreach_vars[0];
  }

  // §12.7.3: the loop variable steps through the array's declared index range,
  // not a fixed zero base. A descending dimension counts down from its high
  // index. Variables, packed vectors, and strings carry no array-info entry
  // and keep the natural zero-based ordering.
  const ArrayInfo* info = arr_name.empty() ? nullptr : ctx.FindArrayInfo(arr_name);

  ctx.PushScope();
  Variable* iter_var = nullptr;
  if (!iter_name.empty()) {
    iter_var = ctx.CreateLocalVariable(iter_name, 32);
  }

  for (uint32_t i = 0; i < size && !ctx.StopRequested(); ++i) {
    if (iter_var) {
      uint32_t index = i;
      if (info) {
        index = info->is_descending ? (info->lo + size - 1 - i) : (info->lo + i);
      }
      iter_var->value = MakeLogic4VecVal(arena, 32, index);
    }
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      ctx.PopScope();
      if (labeled) ctx.PopStaticScope(stmt->label);
      co_return result;
    }
  }

  ctx.PopScope();
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

static ExecTask ExecCycleDelay(const Stmt* stmt, SimContext& ctx,
                               Arena& arena) {
  uint32_t cycles = 0;
  if (stmt->cycle_delay) {
    auto val = EvalExpr(stmt->cycle_delay, ctx, arena);
    cycles = static_cast<uint32_t>(val.ToUint64());
  }
  if (cycles > 0) {
    co_await CycleDelayAwaiter{ctx, cycles};
  }
  if (stmt->body) {
    co_return co_await ExecStmt(stmt->body, ctx, arena);
  }
  co_return StmtResult::kDone;
}

static uint64_t DelayTicksFromValue(const Logic4Vec& val) {
  if (!val.IsKnown()) return 0;
  uint64_t raw = val.ToUint64();
  if (val.is_signed && val.width > 0 && val.width < 64) {
    int64_t signed_val = SignExtend(raw, val.width);
    if (signed_val < 0) return static_cast<uint64_t>(signed_val);
  }
  return raw;
}

static ExecTask ExecDelay(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  uint64_t ticks = 0;
  if (stmt->delay) {
    ticks = DelayTicksFromValue(EvalExpr(stmt->delay, ctx, arena));
  }
  co_await DelayAwaiter{ctx, ticks};
  if (stmt->body) {
    co_return co_await ExecStmt(stmt->body, ctx, arena);
  }
  co_return StmtResult::kDone;
}

static bool IsNamedEvent(const Stmt* stmt, SimContext& ctx) {
  if (stmt->events.size() != 1) return false;
  const auto& ev = stmt->events[0];
  if (ev.edge != Edge::kNone) return false;
  if (!ev.signal || ev.signal->kind != ExprKind::kIdentifier) return false;
  auto* var = ctx.FindVariable(ev.signal->text);
  return var && var->is_event;
}

static bool HasSequenceEvent(const Stmt* stmt) {
  for (const auto& ev : stmt->events) {
    if (ev.is_sequence_event) return true;
  }
  return false;
}

static ExecTask ExecEventControl(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena) {
  if (!stmt->events.empty()) {
    if (HasSequenceEvent(stmt)) {
      co_await SequenceEventAwaiter{ctx, stmt->events};
    } else if (IsNamedEvent(stmt, ctx)) {
      co_await NamedEventAwaiter{ctx, stmt->events[0].signal->text};
    } else {
      co_await EventAwaiter{ctx, stmt->events, arena};
    }
    // §12.4.2.1: a process that suspended on an event control reaches a
    // violation report flush point when it resumes; any unique/priority
    // reports accumulated before the suspension are discarded.
    ctx.FlushPendingViolations();
  }
  if (stmt->body) {
    co_return co_await ExecStmt(stmt->body, ctx, arena);
  }
  co_return StmtResult::kDone;
}

static StmtResult ExecEventTriggerImpl(const Stmt* stmt, SimContext& ctx) {
  if (!stmt->expr || stmt->expr->kind != ExprKind::kIdentifier) {
    return StmtResult::kDone;
  }
  auto* var = ctx.FindVariable(stmt->expr->text);
  if (!var) return StmtResult::kDone;

  if (var->is_null_event) return StmtResult::kDone;

  ctx.SetEventTriggered(stmt->expr->text);

  auto pending = std::move(var->watchers);
  var->watchers.clear();
  auto& sched = ctx.GetScheduler();
  auto region = ctx.IsReactiveContext() ? Region::kReactive : Region::kActive;
  for (auto& cb : pending) {
    auto* event = sched.GetEventPool().Acquire();
    event->callback = std::move(cb);
    sched.ScheduleEvent(ctx.CurrentTime(), region, event);
  }
  return StmtResult::kDone;
}

// Schedules the nonblocking-assignment-region update event that fires a named
// event: it marks the event triggered and wakes every process waiting on it.
// Shared by both the delay/immediate and the event-control forms of ->>.
static void ScheduleNbEventTrigger(Variable* var, std::string_view event_name,
                                   SimTime time, bool reactive,
                                   SimContext& ctx) {
  auto& sched = ctx.GetScheduler();
  auto* nba_event = sched.GetEventPool().Acquire();
  nba_event->callback = [var, event_name, reactive, &ctx]() {
    ctx.SetEventTriggered(event_name);
    auto pending = std::move(var->watchers);
    var->watchers.clear();
    auto& s = ctx.GetScheduler();
    auto wake_region = reactive ? Region::kReactive : Region::kActive;
    for (auto& cb : pending) {
      auto* ev = s.GetEventPool().Acquire();
      ev->callback = std::move(cb);
      s.ScheduleEvent(ctx.CurrentTime(), wake_region, ev);
    }
  };
  sched.ScheduleEvent(time, reactive ? Region::kReNBA : Region::kNBA, nba_event);
}

// The event-control form of ->> reuses the same detached-process machinery that
// an intra-assignment event on a nonblocking assignment uses; declared here,
// defined alongside that machinery below.
static uint64_t EvalRepeatCount(const Expr* count_expr, SimContext& ctx,
                                Arena& arena);
static void SpawnNbaEventProcess(SimCoroutine coro, SimContext& ctx,
                                 Arena& arena);
static SimCoroutine NbEventTriggerEventCoroutine(const Stmt* stmt,
                                                 Variable* var,
                                                 std::string_view event_name,
                                                 uint64_t count, bool reactive,
                                                 SimContext& ctx, Arena& arena);

static StmtResult ExecNbEventTriggerImpl(const Stmt* stmt, SimContext& ctx,
                                         Arena& arena) {
  if (!stmt->expr || stmt->expr->kind != ExprKind::kIdentifier) {
    return StmtResult::kDone;
  }
  auto* var = ctx.FindVariable(stmt->expr->text);
  if (!var) return StmtResult::kDone;

  if (var->is_null_event) return StmtResult::kDone;

  auto event_name = stmt->expr->text;
  bool reactive = ctx.IsReactiveContext();

  // Event-control form: ->> @(...) ev  or  ->> repeat(n) @(...) ev. The update
  // event is created when the event control occurs (after n occurrences for the
  // repeat form), not immediately. ->> never blocks the issuing process, so the
  // wait happens in a spawned process.
  if (!stmt->events.empty()) {
    uint64_t count = 1;
    if (stmt->repeat_event_count) {
      count = EvalRepeatCount(stmt->repeat_event_count, ctx, arena);
      if (count == 0) {
        ScheduleNbEventTrigger(var, event_name, ctx.CurrentTime(), reactive,
                               ctx);
        return StmtResult::kDone;
      }
    }
    SpawnNbaEventProcess(
        NbEventTriggerEventCoroutine(stmt, var, event_name, count, reactive,
                                     ctx, arena),
        ctx, arena);
    return StmtResult::kDone;
  }

  // Delay form (or no timing control): the update event is created when the
  // optional delay expires.
  uint64_t delay = 0;
  if (stmt->delay) delay = EvalExpr(stmt->delay, ctx, arena).ToUint64();
  auto time = ctx.CurrentTime();
  time.ticks += delay;
  ScheduleNbEventTrigger(var, event_name, time, reactive, ctx);
  return StmtResult::kDone;
}

static ExecTask ExecWait(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  std::unordered_set<std::string> reads;
  CollectExprReads(stmt->condition, reads);

  std::unordered_set<std::string> seq_adds;
  std::unordered_set<std::string> seq_removes;
  for (const auto& name : reads) {
    if (ctx.FindSequenceDecl(name)) {
      std::string ep_name = "__seq_" + name;
      auto* ep_var = ctx.FindVariable(ep_name);
      if (!ep_var) {
        ep_var = ctx.CreateVariable(ep_name, 1);
        ep_var->is_event = true;
      }
      seq_adds.insert(ep_name);
      seq_removes.insert(name);
    }
  }
  for (const auto& r : seq_removes) reads.erase(r);
  for (auto& a : seq_adds) reads.insert(std::move(a));
  std::vector<std::string_view> read_vars(reads.begin(), reads.end());
  bool suspended = false;
  while (!ctx.StopRequested()) {
    auto cond = EvalExpr(stmt->condition, ctx, arena);
    if (cond.IsTruthy()) break;
    if (read_vars.empty()) {
      if (labeled) ctx.PopStaticScope(stmt->label);
      co_return StmtResult::kDone;
    }
    suspended = true;
    co_await AnyChangeAwaiter{ctx, read_vars};
  }
  // §12.4.2.1: resuming after suspending on a wait statement is a violation
  // report flush point; drop any reports pending from before the wait.
  if (suspended) ctx.FlushPendingViolations();
  if (stmt->body) {
    auto r = co_await ExecStmt(stmt->body, ctx, arena);
    if (labeled) ctx.PopStaticScope(stmt->label);
    co_return r;
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

struct WaitOrderStepAwaiter {
  SimContext& ctx;
  const std::vector<std::string_view>& event_names;
  std::string_view triggered_name;

  bool await_ready() const noexcept { return false; }

  void await_suspend(std::coroutine_handle<> h) {
    auto done = std::make_shared<bool>(false);
    auto* out = &triggered_name;

    for (auto name : event_names) {
      auto* var = ctx.FindVariable(name);
      if (!var) continue;
      var->AddWatcher([h, name, out, done]() mutable {
        if (*done) return true;
        *done = true;
        *out = name;
        h.resume();
        return true;
      });
    }
  }

  std::string_view await_resume() const noexcept { return triggered_name; }
};

static ExecTask ExecWaitOrder(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  auto& events = stmt->wait_order_events;
  if (events.empty()) {
    if (stmt->then_branch) {
      co_return co_await ExecStmt(stmt->then_branch, ctx, arena);
    }
    co_return StmtResult::kDone;
  }

  bool failed = false;

  for (size_t i = 0; i < events.size() && !failed; ++i) {
    auto expected_name = events[i]->text;

    if (i == 0 && ctx.IsEventTriggered(expected_name)) {
      continue;
    }

    std::vector<std::string_view> remaining;
    for (size_t j = i; j < events.size(); ++j) {
      remaining.push_back(events[j]->text);
    }

    auto triggered = co_await WaitOrderStepAwaiter{ctx, remaining, {}};

    if (triggered != expected_name) {
      failed = true;
    }
  }

  if (failed) {
    if (stmt->else_branch) {
      co_return co_await ExecStmt(stmt->else_branch, ctx, arena);
    }

    // §15.5.4: when no else (fail) clause is supplied, a failed sequence
    // raises a default run-time error by calling $error (see §20.10), which
    // records ERROR severity and lets the run continue.
    EmitSeverityHeader(ctx, "ERROR",
                       "wait_order events triggered out of order", std::cerr);
    co_return StmtResult::kDone;
  }

  if (stmt->then_branch) {
    co_return co_await ExecStmt(stmt->then_branch, ctx, arena);
  }
  co_return StmtResult::kDone;
}

static SimCoroutine ForkChildCoroutine(const Stmt* body, SimContext& ctx,
                                       Arena& arena, ForkJoinState* state,
                                       WaitForkState* parent_wfs,
                                       Process* parent_proc) {
  co_await ExecStmt(body, ctx, arena);

  auto* child_proc = ctx.CurrentProcess();
  if (child_proc && child_proc->sv_state != ProcessState::kKilled) {
    child_proc->sv_state = ProcessState::kFinished;
    for (auto& w : child_proc->await_waiters) {
      if (w) w.resume();
    }
    child_proc->await_waiters.clear();
  }
  state->remaining--;
  bool should_resume =
      state->join_any ? !state->resumed : (state->remaining == 0);
  if (should_resume && state->parent) {
    state->resumed = true;
    // §18.14.2: restore the spawning thread as current before the join site
    // resumes so its subsequent draws come from its own RNG, not from
    // whichever child happened to run last.
    if (state->parent_proc) ctx.SetCurrentProcess(state->parent_proc);
    state->parent.resume();
  }
  if (parent_wfs && --parent_wfs->remaining == 0 && parent_wfs->waiter) {
    ctx.SetCurrentProcess(parent_proc);
    parent_wfs->waiter.resume();
  }
}

static bool IsForkBlockItemDecl(const Stmt* s) {
  return s->kind == StmtKind::kVarDecl || s->kind == StmtKind::kBlockItemDecl;
}

static ExecTask ExecFork(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  if (stmt->fork_stmts.empty()) {
    if (labeled) ctx.PopStaticScope(stmt->label);
    co_return StmtResult::kDone;
  }

  uint32_t process_count = 0;
  for (auto* s : stmt->fork_stmts) {
    if (IsForkBlockItemDecl(s)) {
      co_await ExecStmt(s, ctx, arena);
    } else {
      process_count++;
    }
  }

  if (process_count == 0) {
    if (labeled) ctx.PopStaticScope(stmt->label);
    co_return StmtResult::kDone;
  }

  auto* state = arena.Create<ForkJoinState>();
  state->remaining = process_count;
  state->join_any = (stmt->join_kind == TokenKind::kKwJoinAny);

  auto* spawning_proc = ctx.CurrentProcess();
  state->parent_proc = spawning_proc;

  // §9.6.1: wait fork blocks until every immediate child subprocess of the
  // current process has terminated, irrespective of how the child was
  // spawned. Register each child against the spawning process's wait-fork
  // tally for all join kinds, not just join_none: after join_any the
  // unblocked siblings keep running and a later wait fork must still wait on
  // them. (For plain join the count is already drained by the join site, so
  // the extra bookkeeping is inert.)
  Process* parent_proc = spawning_proc;
  WaitForkState* parent_wfs =
      parent_proc ? &parent_proc->wait_fork_state : nullptr;

  for (auto* s : stmt->fork_stmts) {
    if (IsForkBlockItemDecl(s)) continue;
    if (parent_wfs) parent_wfs->remaining++;
    auto* p = arena.Create<Process>();
    if (spawning_proc) spawning_proc->children.push_back(p);
    p->kind = ProcessKind::kInitial;
    if (spawning_proc) {
      p->is_reactive = spawning_proc->is_reactive;
      p->home_region = spawning_proc->home_region;
      p->program_block_id = spawning_proc->program_block_id;
    }
    // §18.14.2: a new thread's RNG is initialized with the next random value
    // drawn from the thread that creates it. Each child therefore receives a
    // unique seed determined solely by the parent, and the per-child seed
    // material is settled in fork order rather than execution order.
    p->rng_seed = ctx.DrawSeedForChild();
    p->coro =
        ForkChildCoroutine(s, ctx, arena, state, parent_wfs, parent_proc)
            .Release();

    if (s->kind == StmtKind::kExprStmt && s->expr) {
      std::string_view task_name;
      if (s->expr->kind == ExprKind::kCall)
        task_name = s->expr->callee;
      else if (s->expr->kind == ExprKind::kIdentifier)
        task_name = s->expr->text;
      if (!task_name.empty() && ctx.FindFunction(task_name))
        ctx.RegisterNamedScope(task_name, p);
    }
    if (s->kind == StmtKind::kBlock && !s->label.empty())
      ctx.RegisterNamedScope(s->label, p);

    for (auto scope : ctx.ActiveNamedScopes())
      ctx.RegisterNamedScope(scope, p);
    auto* event = ctx.GetScheduler().GetEventPool().Acquire();
    event->callback = [p, &ctx, state, parent_wfs, parent_proc]() {
      if (!p->active) {

        state->remaining--;
        bool should_resume =
            state->join_any ? !state->resumed : (state->remaining == 0);
        if (should_resume && state->parent) {
          state->resumed = true;
          state->parent.resume();
        }
        if (parent_wfs && --parent_wfs->remaining == 0 && parent_wfs->waiter) {
          ctx.SetCurrentProcess(parent_proc);
          parent_wfs->waiter.resume();
        }
        return;
      }
      ctx.SetCurrentProcess(p);
      p->Resume();
    };
    auto fork_region =
        (spawning_proc && spawning_proc->is_reactive) ? Region::kReactive
                                                      : Region::kActive;
    ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), fork_region, event);
  }

  if (stmt->join_kind != TokenKind::kKwJoinNone) {
    co_await ForkJoinAwaiter{state};
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

static ExecTask ExecWaitFork(SimContext& ctx) {
  auto* proc = ctx.CurrentProcess();
  if (!proc) co_return StmtResult::kDone;
  co_await WaitForkAwaiter{&proc->wait_fork_state};
  co_return StmtResult::kDone;
}

static void RunDeferredActionSync(const Stmt* action, SimContext& ctx,
                                  Arena& arena) {
  if (!action) return;
  switch (action->kind) {
    case StmtKind::kNull:
      return;
    case StmtKind::kExprStmt:

      EvalExpr(action->expr, ctx, arena);
      return;
    case StmtKind::kBlockingAssign:

      ExecBlockingAssignImpl(action, ctx, arena);
      return;
    default:

      return;
  }
}

static void SnapshotDeferredCallArgs(const Stmt* action, SimContext& ctx,
                                     Arena& arena) {
  if (!action || action->kind != StmtKind::kExprStmt || !action->expr) return;
  if (action->expr->kind != ExprKind::kCall &&
      action->expr->kind != ExprKind::kSystemCall) {
    return;
  }
  for (auto* arg : action->expr->args) {
    if (!arg) continue;
    auto val = EvalExpr(arg, ctx, arena);
    ctx.SetDeferredArgSnapshot(arg, val);
  }
}

static void ClearDeferredCallArgSnapshots(const Stmt* action,
                                          SimContext& ctx) {
  if (!action || action->kind != StmtKind::kExprStmt || !action->expr) return;
  if (action->expr->kind != ExprKind::kCall &&
      action->expr->kind != ExprKind::kSystemCall) {
    return;
  }
  for (auto* arg : action->expr->args) {
    if (!arg) continue;
    ctx.ClearDeferredArgSnapshot(arg);
  }
}

static void ScheduleDeferredAction(const Stmt* action, bool is_final_deferred,
                                   SimContext& ctx, Arena& arena) {
  if (!action) return;

  SnapshotDeferredCallArgs(action, ctx, arena);
  Region region =
      is_final_deferred ? Region::kPostponed : Region::kReactive;
  auto* ev = ctx.GetScheduler().GetEventPool().Acquire();
  ev->callback = [action, &ctx, &arena]() {
    RunDeferredActionSync(action, ctx, arena);

    ClearDeferredCallArgSnapshots(action, ctx);
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), region, ev);
}

static ExecTask ExecImmediateAssert(const Stmt* stmt, SimContext& ctx,
                                    Arena& arena) {
  auto cond = EvalExpr(stmt->assert_expr, ctx, arena);

  bool is_true = cond.IsTruthy();
  if (stmt->kind == StmtKind::kCoverImmediate) {
    ctx.IncrementCoverEvalCount();
  }
  if (is_true) {
    if (stmt->kind == StmtKind::kCoverImmediate) {
      ctx.IncrementCoverSuccessCount();
    }
    if (stmt->assert_pass_stmt) {

      if (stmt->is_deferred) {
        ScheduleDeferredAction(stmt->assert_pass_stmt,
                               stmt->is_final_deferred, ctx, arena);
        co_return StmtResult::kDone;
      }
      co_return co_await ExecStmt(stmt->assert_pass_stmt, ctx, arena);
    }
  } else {
    if (stmt->assert_fail_stmt) {
      if (stmt->is_deferred) {
        ScheduleDeferredAction(stmt->assert_fail_stmt,
                               stmt->is_final_deferred, ctx, arena);
        co_return StmtResult::kDone;
      }
      co_return co_await ExecStmt(stmt->assert_fail_stmt, ctx, arena);
    } else if (stmt->kind != StmtKind::kCoverImmediate) {

      ctx.IncrementAssertionFailCount();
      EmitSeverityHeader(ctx, "ERROR", "Assertion failed.", std::cerr);
    }
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecProcessAwait(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  MethodCallParts parts;
  if (ExtractMethodCallParts(expr, parts) &&
      ctx.GetVariableClassType(parts.var_name) == "process" &&
      parts.method_name == "await") {
    auto* var = ctx.FindVariable(parts.var_name);
    if (var) {
      auto proc_handle = var->value.ToUint64();
      auto* proc = ctx.FindProcessByHandle(proc_handle);
      if (proc) {

        if (proc->kind == ProcessKind::kFinal ||
            proc->kind == ProcessKind::kContAssign) {
          ctx.GetDiag().Error(
              {}, "await() shall only target a process created by an initial "
                  "procedure, always procedure, or fork block");
          co_return StmtResult::kDone;
        }

        if (proc == ctx.CurrentProcess()) {
          ctx.GetDiag().Error(
              {}, "process cannot await its own termination");
          co_return StmtResult::kDone;
        }
        co_await ProcessAwaitAwaiter{proc};
      }
    }
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecInlineTaskCall(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  auto* expr = stmt->expr;

  // $cast invoked as a task: the evaluation performs the assignment when the
  // cast is valid and leaves the destination untouched otherwise. Unlike the
  // function form (which simply reports 0), the task form signals an invalid
  // assignment with a run-time error.
  if (expr && expr->kind == ExprKind::kSystemCall && expr->callee == "$cast") {
    auto result = EvalExpr(expr, ctx, arena);
    if (result.ToUint64() == 0) {
      ctx.GetDiag().Error(expr->loc,
                          "$cast task could not assign the source expression "
                          "to the destination; assignment is invalid");
    }
    co_return StmtResult::kDone;
  }

  // §20.17.2: invoked as a task, $stacktrace displays the call stack of the
  // context calling it, up to the top-level process. The function form, which
  // instead returns the same text as a string, is evaluated as an expression.
  if (expr && expr->kind == ExprKind::kSystemCall &&
      expr->callee == "$stacktrace") {
    std::cout << BuildStackTraceReport(ctx) << "\n";
    co_return StmtResult::kDone;
  }

  {
    MethodCallParts parts;
    if (ExtractMethodCallParts(expr, parts) &&
        ctx.GetVariableClassType(parts.var_name) == "process" &&
        parts.method_name == "await") {
      co_return co_await ExecProcessAwait(expr, ctx, arena);
    }
  }
  auto* func = SetupTaskCall(expr, ctx, arena);
  if (!func) {
    EvalExpr(expr, ctx, arena);
    co_return StmtResult::kDone;
  }
  bool has_name = !func->name.empty();
  if (has_name) {
    ctx.RegisterNamedScope(func->name, ctx.CurrentProcess());
    ctx.PushActiveNamedScope(func->name);
  }
  for (auto* s : func->func_body_stmts) {
    auto result = co_await ExecStmt(s, ctx, arena);
    if (result == StmtResult::kReturn) break;
    if (result == StmtResult::kDisable) {
      if (has_name && ctx.GetDisableTarget() == func->name) {
        ctx.ClearDisableTarget();
        break;
      }
      if (has_name) {
        ctx.PopActiveNamedScope();
        ctx.UnregisterNamedScope(func->name, ctx.CurrentProcess());
      }
      TeardownTaskCall(func, expr, ctx, arena);
      co_return StmtResult::kDisable;
    }
  }
  if (has_name) {
    ctx.PopActiveNamedScope();
    ctx.UnregisterNamedScope(func->name, ctx.CurrentProcess());
  }
  TeardownTaskCall(func, expr, ctx, arena);
  co_return StmtResult::kDone;
}

static ExecTask ExecBlockingAssignTimed(const Stmt* stmt, SimContext& ctx,
                                        Arena& arena) {
  auto rhs_val = EvalExpr(stmt->rhs, ctx, arena);
  auto delay_val = EvalExpr(stmt->delay, ctx, arena);
  co_await DelayAwaiter{ctx, delay_val.ToUint64()};
  PerformBlockingAssign(stmt->lhs, rhs_val, ctx, arena);
  co_return StmtResult::kDone;
}

static ExecTask ExecBlockingAssignEvent(const Stmt* stmt, SimContext& ctx,
                                        Arena& arena) {
  auto rhs_val = EvalExpr(stmt->rhs, ctx, arena);
  co_await EventAwaiter{ctx, stmt->events, arena};
  PerformBlockingAssign(stmt->lhs, rhs_val, ctx, arena);
  co_return StmtResult::kDone;
}

static uint64_t EvalRepeatCount(const Expr* count_expr, SimContext& ctx,
                                Arena& arena) {
  auto val = EvalExpr(count_expr, ctx, arena);
  if (!val.IsKnown()) return 0;
  uint64_t count = val.ToUint64();
  if (val.is_signed && static_cast<int64_t>(count) <= 0) return 0;
  return count;
}

static ExecTask ExecBlockingAssignRepeatEvent(const Stmt* stmt,
                                              SimContext& ctx, Arena& arena) {
  auto rhs_val = EvalExpr(stmt->rhs, ctx, arena);
  uint64_t count = EvalRepeatCount(stmt->repeat_event_count, ctx, arena);
  if (count > 0) {
    co_await RepeatEventAwaiter{ctx, stmt->events, arena, count};
  }
  PerformBlockingAssign(stmt->lhs, rhs_val, ctx, arena);
  co_return StmtResult::kDone;
}

static SimCoroutine NbaEventCoroutine(const Stmt* stmt, Logic4Vec rhs_val,
                                      SimContext& ctx, Arena& arena) {
  co_await EventAwaiter{ctx, stmt->events, arena};
  ScheduleNonblockingAssign(stmt, rhs_val, 0, ctx, arena);
}

static SimCoroutine NbaRepeatEventCoroutine(const Stmt* stmt,
                                            Logic4Vec rhs_val, uint64_t count,
                                            SimContext& ctx, Arena& arena) {
  co_await RepeatEventAwaiter{ctx, stmt->events, arena, count};
  ScheduleNonblockingAssign(stmt, rhs_val, 0, ctx, arena);
}

static void SpawnNbaEventProcess(SimCoroutine coro, SimContext& ctx,
                                 Arena& arena) {
  auto* p = arena.Create<Process>();
  p->kind = ProcessKind::kInitial;
  p->coro = coro.Release();
  auto* parent = ctx.CurrentProcess();
  if (parent && parent->is_reactive) {
    p->is_reactive = true;
    p->home_region = Region::kReactive;
  }
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->callback = [p, &ctx]() {
    ctx.SetCurrentProcess(p);
    p->Resume();
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), p->home_region, event);
}

static StmtResult ExecNbaWithEvent(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena) {
  auto rhs_val = EvalExpr(stmt->rhs, ctx, arena);
  if (stmt->repeat_event_count) {
    uint64_t count = EvalRepeatCount(stmt->repeat_event_count, ctx, arena);
    if (count == 0) {
      ScheduleNonblockingAssign(stmt, rhs_val, 0, ctx, arena);
      return StmtResult::kDone;
    }
    SpawnNbaEventProcess(
        NbaRepeatEventCoroutine(stmt, rhs_val, count, ctx, arena), ctx, arena);
  } else {
    SpawnNbaEventProcess(NbaEventCoroutine(stmt, rhs_val, ctx, arena), ctx,
                         arena);
  }
  return StmtResult::kDone;
}

// Detached waiter for the event-control form of ->>: blocks (off the issuing
// process) until the event control has occurred the required number of times,
// then creates the nonblocking-region update event that fires the named event.
static SimCoroutine NbEventTriggerEventCoroutine(const Stmt* stmt,
                                                 Variable* var,
                                                 std::string_view event_name,
                                                 uint64_t count, bool reactive,
                                                 SimContext& ctx,
                                                 Arena& arena) {
  for (uint64_t i = 0; i < count; ++i) {
    co_await EventAwaiter{ctx, stmt->events, arena};
  }
  ScheduleNbEventTrigger(var, event_name, ctx.CurrentTime(), reactive, ctx);
}

static StmtResult ExecDisableImpl(const Stmt* stmt, SimContext& ctx) {
  if (!stmt->expr || stmt->expr->kind != ExprKind::kIdentifier)
    return StmtResult::kDone;

  auto target = stmt->expr->text;
  if (target.empty()) return StmtResult::kDone;

  auto* current = ctx.CurrentProcess();

  auto procs = ctx.FindNamedScopeProcesses(target);
  bool self_disable = false;

  for (auto* proc : procs) {
    if (proc == current) {
      self_disable = true;
      continue;
    }

    proc->active = false;
  }

  if (self_disable) {
    ctx.SetDisableTarget(target);
    return StmtResult::kDisable;
  }

  return StmtResult::kDone;
}

static void DisableDescendants(Process* proc) {
  for (auto* child : proc->children) {
    child->active = false;
    DisableDescendants(child);
  }
}

static StmtResult ExecDisableForkImpl(SimContext& ctx) {
  auto* proc = ctx.CurrentProcess();
  if (!proc) return StmtResult::kDone;
  DisableDescendants(proc);
  proc->wait_fork_state.remaining = 0;
  proc->children.clear();
  return StmtResult::kDone;
}

ExecTask ExecStmt(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt) return ExecTask::Immediate(StmtResult::kDone);

  switch (stmt->kind) {
    case StmtKind::kNull:
      return ExecTask::Immediate(StmtResult::kDone);
    case StmtKind::kBlock:
      return ExecBlock(stmt, ctx, arena);
    case StmtKind::kIf:
      return ExecIf(stmt, ctx, arena);
    case StmtKind::kCase:
      return ExecCase(stmt, ctx, arena);
    case StmtKind::kFor:
      return ExecFor(stmt, ctx, arena);
    case StmtKind::kForeach:
      return ExecForeach(stmt, ctx, arena);
    case StmtKind::kWhile:
      return ExecWhile(stmt, ctx, arena);
    case StmtKind::kForever:
      return ExecForever(stmt, ctx, arena);
    case StmtKind::kRepeat:
      return ExecRepeat(stmt, ctx, arena);
    case StmtKind::kDoWhile:
      return ExecDoWhile(stmt, ctx, arena);
    case StmtKind::kBlockingAssign:
      if (stmt->delay) return ExecBlockingAssignTimed(stmt, ctx, arena);
      if (!stmt->events.empty()) {
        if (stmt->repeat_event_count)
          return ExecBlockingAssignRepeatEvent(stmt, ctx, arena);
        return ExecBlockingAssignEvent(stmt, ctx, arena);
      }
      return ExecTask::Immediate(ExecBlockingAssignImpl(stmt, ctx, arena));
    case StmtKind::kNonblockingAssign:
      if (!stmt->events.empty())
        return ExecTask::Immediate(ExecNbaWithEvent(stmt, ctx, arena));
      return ExecTask::Immediate(ExecNonblockingAssignImpl(stmt, ctx, arena));
    case StmtKind::kExprStmt:
      return ExecInlineTaskCall(stmt, ctx, arena);
    case StmtKind::kDelay:
      return ExecDelay(stmt, ctx, arena);
    case StmtKind::kCycleDelay:
      return ExecCycleDelay(stmt, ctx, arena);
    case StmtKind::kEventControl:
      return ExecEventControl(stmt, ctx, arena);
    case StmtKind::kFork:
      return ExecFork(stmt, ctx, arena);
    case StmtKind::kWait:
      return ExecWait(stmt, ctx, arena);
    case StmtKind::kEventTrigger:
      return ExecTask::Immediate(ExecEventTriggerImpl(stmt, ctx));
    case StmtKind::kNbEventTrigger:
      return ExecTask::Immediate(ExecNbEventTriggerImpl(stmt, ctx, arena));
    case StmtKind::kWaitOrder:
      return ExecWaitOrder(stmt, ctx, arena);
    case StmtKind::kTimingControl:
      return ExecTask::Immediate(StmtResult::kDone);
    case StmtKind::kDisable:
      return ExecTask::Immediate(ExecDisableImpl(stmt, ctx));
    case StmtKind::kDisableFork:
      return ExecTask::Immediate(ExecDisableForkImpl(ctx));
    case StmtKind::kWaitFork:
      return ExecWaitFork(ctx);
    case StmtKind::kBreak:
      return ExecTask::Immediate(StmtResult::kBreak);
    case StmtKind::kContinue:
      return ExecTask::Immediate(StmtResult::kContinue);
    case StmtKind::kReturn:
      // §18.17.7: inside a randsequence production with a non-void return type,
      // a 'return <expr>' assigns its value to the production. The engine has
      // pointed the return slot at the production's return storage, so evaluate
      // the expression into it here. Outside that context the slot is null and
      // the return simply unwinds.
      if (stmt->expr && ctx.RsReturnSlot() != nullptr) {
        *ctx.RsReturnSlot() =
            EvalExpr(stmt->expr, ctx, arena, ctx.RsReturnSlot()->width);
      }
      return ExecTask::Immediate(StmtResult::kReturn);
    case StmtKind::kAssertImmediate:
    case StmtKind::kAssumeImmediate:
    case StmtKind::kCoverImmediate:
    case StmtKind::kExpect:
      return ExecImmediateAssert(stmt, ctx, arena);
    case StmtKind::kForce:
    case StmtKind::kAssign:
      return ExecTask::Immediate(ExecForceOrAssignImpl(stmt, ctx, arena));
    case StmtKind::kRelease:
    case StmtKind::kDeassign:
      return ExecTask::Immediate(ExecReleaseOrDeassignImpl(stmt, ctx, arena));
    case StmtKind::kRandcase:
      return ExecRandcase(stmt, ctx, arena);
    case StmtKind::kRandsequence:
      return ExecRandsequence(stmt, ctx, arena);
    case StmtKind::kVarDecl:
      return ExecTask::Immediate(ExecVarDeclImpl(stmt, ctx, arena));
    default:
      return ExecTask::Immediate(StmtResult::kDone);
  }
}

bool IsTimeControlStatement(StmtKind kind) {
  return kind == StmtKind::kDelay || kind == StmtKind::kEventControl;
}

}
