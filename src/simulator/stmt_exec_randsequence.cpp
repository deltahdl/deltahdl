#include <cmath>
#include <cstddef>
#include <cstdint>
#include <format>
#include <optional>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_stmt.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/exec_task.h"
#include "simulator/scope.h"
#include "simulator/sim_context.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/stmt_exec_randsequence_internal.h"
#include "simulator/stmt_result.h"

namespace delta {

static uint64_t DrawBelow(uint64_t total, SimContext& ctx) {
  if (total <= 0xFFFFFFFFULL) return ctx.Urandom32() % total;
  uint64_t hi = ctx.Urandom32();
  uint64_t lo = ctx.Urandom32();
  return ((hi << 32) | lo) % total;
}

const Stmt* SelectRandcaseBranch(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena) {
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
    return nullptr;
  }

  uint64_t pick = DrawBelow(total_weight, ctx);
  uint64_t cumulative = 0;
  for (size_t i = 0; i < stmt->randcase_items.size(); ++i) {
    cumulative += weights[i];
    if (pick < cumulative) return stmt->randcase_items[i].second;
  }
  return nullptr;
}

ExecTask ExecRandcase(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  const Stmt* branch = SelectRandcaseBranch(stmt, ctx, arena);
  if (branch == nullptr) co_return StmtResult::kDone;
  co_return co_await ExecStmt(branch, ctx, arena);
}

static ExecTask ExecRsProduction(const Stmt* stmt, const RsProductionItem& call,
                                 SimContext& ctx, Arena& arena,
                                 RuleValueCapture* cap);

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
std::vector<std::optional<Logic4Vec>> EvalProductionActuals(
    const RsProduction* production, const RsProductionItem& call,
    SimContext& ctx, Arena& arena);
void BindProductionFormals(const RsProduction* production,
                           const std::vector<std::optional<Logic4Vec>>& actuals,
                           SimContext& ctx, Arena& arena);

const RsProduction* FindProduction(const Stmt* stmt, std::string_view name) {
  for (const auto& prod : stmt->rs_productions) {
    if (prod.name == name) return &prod;
  }
  return nullptr;
}

bool ProductionReturnsValue(const RsProduction* p) {
  return p != nullptr && p->has_return_type &&
         p->return_type.kind != DataTypeKind::kVoid;
}

bool ProductionReturnsString(const RsProduction* p) {
  return p != nullptr && p->has_return_type &&
         p->return_type.kind == DataTypeKind::kString;
}

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

static uint64_t RepeatCount(const RsProd& prod, SimContext& ctx, Arena& arena);

static ExecTask ExecRsProdRepeat(const Stmt* stmt, const RsProd& prod,
                                 SimContext& ctx, Arena& arena,
                                 RuleValueCapture* cap) {
  uint64_t count = RepeatCount(prod, ctx, arena);
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

static bool WeightIsNegative(const Logic4Vec& v) {
  if (!v.is_signed || v.width == 0 || v.nwords == 0) return false;
  uint32_t top = v.width - 1;
  return ((v.words[top / 64].aval >> (top % 64)) & 1ULL) != 0;
}

struct NonNegativeRule {
  std::string_view what;
  std::string_view noun;
  Subclause rule;
};

static uint64_t NonNegativeOrReport(const Logic4Vec& val, const Expr* e,
                                    const NonNegativeRule& rule,
                                    SimContext& ctx) {
  if (!val.IsKnown()) {
    ctx.GetDiag().Error(
        e->range.start,
        std::format("randsequence {} has unknown bits; {} needs a known "
                    "integral value of zero or more",
                    rule.what, rule.noun),
        rule.rule);
    return 0;
  }
  if (WeightIsNegative(val)) {
    ctx.GetDiag().Error(
        e->range.start,
        std::format("randsequence {} is negative; {} needs a known integral "
                    "value of zero or more",
                    rule.what, rule.noun),
        rule.rule);
    return 0;
  }
  return val.ToUint64();
}

static uint64_t RepeatCount(const RsProd& prod, SimContext& ctx, Arena& arena) {
  constexpr NonNegativeRule kRepeatCount{"repeat count", "a repeat count",
                                         Subclause("18.17.4")};
  return NonNegativeOrReport(EvalExpr(prod.repeat_count, ctx, arena),
                             prod.repeat_count, kRepeatCount, ctx);
}

static const RsRule& SelectRule(const RsProduction& production, SimContext& ctx,
                                Arena& arena) {
  constexpr NonNegativeRule kRuleWeight{"rule weight", "a weight",
                                        Subclause("18.17.1")};
  if (production.rules.size() <= 1) return production.rules[0];
  std::vector<uint64_t> weights;
  weights.reserve(production.rules.size());
  uint64_t total_weight = 0;
  for (const auto& rule : production.rules) {
    uint64_t w = 1;
    if (rule.weight) {
      w = NonNegativeOrReport(EvalExpr(rule.weight, ctx, arena), rule.weight,
                              kRuleWeight, ctx);
    }
    weights.push_back(w);
    total_weight += w;
  }
  if (total_weight == 0) return production.rules[0];
  uint64_t pick = DrawBelow(total_weight, ctx);

  uint64_t cumulative = 0;
  for (size_t i = 0; i + 1 < production.rules.size(); ++i) {
    cumulative += weights[i];
    if (pick < cumulative) return production.rules[i];
  }
  return production.rules.back();
}

static double EvalRandJoinBias(Expr* expr, SimContext& ctx, Arena& arena) {
  if (!expr) return 0.5;
  auto v = EvalExpr(expr, ctx, arena);
  double f = v.is_real ? RealVecToDouble(v) : static_cast<double>(v.ToUint64());
  if (f >= 0.0 && f <= 1.0) return f;
  ctx.GetDiag().Error(expr->range.start,
                      "rand join expression lies outside 0.0 to 1.0; it needs "
                      "a real number in that range",
                      Subclause("18.17.5"));
  return f < 0.0 ? 0.0 : 1.0;
}

namespace {
struct RandJoinSeq {
  std::vector<const RsProd*> steps;
  size_t cursor = 0;
  const RsProductionItem* item = nullptr;
  const RsProduction* production = nullptr;
  const RsRule* rule = nullptr;
  std::vector<Scope> scopes;
  RuleValueCapture cap;
  Logic4Vec ret_value;
  bool returns_value = false;
  size_t Remaining() const { return steps.size() - cursor; }
};
}  // namespace

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

static size_t ChooseRandJoinOperand(const std::vector<RandJoinSeq>& seqs,
                                    double exponent, SimContext& ctx) {
  double total = 0.0;
  for (const auto& seq : seqs) {
    if (seq.Remaining() > 0)
      total += std::pow(static_cast<double>(seq.Remaining()), exponent);
  }
  if (total <= 0.0) return seqs.size();

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
    for (size_t i = seqs.size(); i-- > 0;) {
      if (seqs[i].Remaining() > 0) {
        chosen = i;
        break;
      }
    }
  }
  return chosen;
}

static ExecTask RunRandJoinRuleWeightCode(const RsRule& rule, SimContext& ctx,
                                          Arena& arena) {
  ctx.PushScope();
  StmtResult block_result = StmtResult::kDone;
  for (auto* s : rule.weight_code) {
    auto r = co_await ExecStmt(s, ctx, arena);
    if (ClassifyRandseqResult(r) != RandseqAction::kKeepGenerating) {
      block_result = r;
      break;
    }
    if (ctx.StopRequested()) break;
  }
  ctx.PopScope();
  co_return block_result;
}

namespace {
struct RandseqEngine {
  const Stmt* stmt;
  SimContext& ctx;
  Arena& arena;
};
}  // namespace

static ExecTask BuildOneRandJoinSeq(const RandseqEngine& eng,
                                    const RsProductionItem& item,
                                    RandJoinSeq& seq) {
  const auto* production = FindProduction(eng.stmt, item.name);
  if (!production) co_return StmtResult::kDone;
  seq.item = &item;
  seq.production = production;
  seq.returns_value = ProductionReturnsValue(production);
  if (seq.returns_value) {
    uint32_t w = DeclaredTypeWidth(production->return_type, eng.ctx);
    if (w == 0 && !ProductionReturnsString(production)) w = 32;
    seq.ret_value = MakeLogic4VecVal(eng.arena, w, 0);
  }
  std::vector<std::optional<Logic4Vec>> actuals =
      EvalProductionActuals(production, item, eng.ctx, eng.arena);

  std::vector<Scope> caller = eng.ctx.SwapScopeStack({});
  eng.ctx.SwapScopeStack(caller);
  eng.ctx.PushScope();
  BindProductionFormals(production, actuals, eng.ctx, eng.arena);
  seq.rule = &SelectRule(*production, eng.ctx, eng.arena);
  CollectRandJoinSteps(*seq.rule, eng.arena, seq.steps);
  seq.cap = BuildStepValueCapture(eng.stmt, seq.steps, eng.ctx);
  seq.scopes = eng.ctx.SwapScopeStack(std::move(caller));
  co_return StmtResult::kDone;
}

static ExecTask BuildRandJoinSeqs(const RandseqEngine& eng,
                                  const RsRule& selected,
                                  std::vector<RandJoinSeq>& seqs) {
  seqs.reserve(selected.rand_join_items.size());
  for (const auto& item : selected.rand_join_items) {
    RandJoinSeq seq;
    co_await BuildOneRandJoinSeq(eng, item, seq);
    seqs.push_back(std::move(seq));
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecOneRandJoinStep(const RandseqEngine& eng,
                                    RandJoinSeq& seq) {
  const RsProd* step = seq.steps[seq.cursor++];
  std::vector<Scope> caller = eng.ctx.SwapScopeStack(std::move(seq.scopes));
  Logic4Vec* prev_slot =
      eng.ctx.SetRsReturnSlot(seq.returns_value ? &seq.ret_value : nullptr);
  auto result =
      co_await ExecRsProd(eng.stmt, *step, eng.ctx, eng.arena, &seq.cap);
  eng.ctx.SetRsReturnSlot(prev_slot);
  seq.scopes = eng.ctx.SwapScopeStack(std::move(caller));
  co_return result;
}

static void StoreRandJoinOperandValue(const RandJoinSeq& seq,
                                      const RuleValueCapture& cap,
                                      SimContext& ctx, Arena& arena) {
  if (!seq.returns_value) return;
  RuleProductionSlot slot =
      SlotForAppearance(&cap, *seq.item, seq.production->name);
  if (slot.idx == 0) return;
  Logic4Vec value = ProductionReturnsString(seq.production)
                        ? StripStringZeros(seq.ret_value, arena)
                        : seq.ret_value;
  StoreRuleProductionValue(slot, seq.production, value, ctx, arena);
}

static ExecTask ExecRandJoinItems(const Stmt* stmt, const RsRule& selected,
                                  SimContext& ctx, Arena& arena) {
  double bias = EvalRandJoinBias(selected.rand_join_expr, ctx, arena);

  RuleValueCapture cap = BuildRuleValueCapture(stmt, selected, ctx);

  std::vector<RandJoinSeq> seqs;
  RandseqEngine eng{stmt, ctx, arena};
  co_await BuildRandJoinSeqs(eng, selected, seqs);

  double exponent = 4.0 * bias - 1.0;
  while (!ctx.StopRequested()) {
    size_t chosen = ChooseRandJoinOperand(seqs, exponent, ctx);
    if (chosen == seqs.size()) break;

    auto result = co_await ExecOneRandJoinStep(eng, seqs[chosen]);
    auto action = ClassifyRandseqResult(result);
    if (action == RandseqAction::kUnwind) co_return result;
    if (action == RandseqAction::kAbortProduction) {
      seqs[chosen].cursor = seqs[chosen].steps.size();
    }
    if (seqs[chosen].Remaining() == 0) {
      std::vector<Scope> caller =
          ctx.SwapScopeStack(std::move(seqs[chosen].scopes));
      Logic4Vec* prev_slot = ctx.SetRsReturnSlot(
          seqs[chosen].returns_value ? &seqs[chosen].ret_value : nullptr);
      auto block =
          co_await RunRandJoinRuleWeightCode(*seqs[chosen].rule, ctx, arena);
      ctx.SetRsReturnSlot(prev_slot);
      seqs[chosen].scopes = ctx.SwapScopeStack(std::move(caller));
      if (ClassifyRandseqResult(block) == RandseqAction::kUnwind) {
        co_return block;
      }
      StoreRandJoinOperandValue(seqs[chosen], cap, ctx, arena);
    }
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecRuleProds(const Stmt* stmt, const RsRule& selected,
                              SimContext& ctx, Arena& arena) {
  RuleValueCapture cap = BuildRuleValueCapture(stmt, selected, ctx);
  for (const auto& prod : selected.prods) {
    auto result = co_await ExecRsProd(stmt, prod, ctx, arena, &cap);
    if (ClassifyRandseqResult(result) != RandseqAction::kKeepGenerating) {
      co_return result;
    }
    if (ctx.StopRequested()) break;
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecSelectedRule(const Stmt* stmt, const RsRule& selected,
                                 SimContext& ctx, Arena& arena) {
  StmtResult prods_result = StmtResult::kDone;
  if (selected.is_rand_join) {
    prods_result = co_await ExecRandJoinItems(stmt, selected, ctx, arena);
  } else {
    prods_result = co_await ExecRuleProds(stmt, selected, ctx, arena);
  }
  if (prods_result != StmtResult::kDone) co_return prods_result;
  ctx.PushScope();
  StmtResult block_result = StmtResult::kDone;
  for (auto* s : selected.weight_code) {
    auto result = co_await ExecStmt(s, ctx, arena);
    if (ClassifyRandseqResult(result) != RandseqAction::kKeepGenerating) {
      block_result = result;
      break;
    }
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

  std::vector<std::optional<Logic4Vec>> actuals =
      EvalProductionActuals(production, call, ctx, arena);

  ctx.PushScope();
  BindProductionFormals(production, actuals, ctx, arena);

  Logic4Vec ret_value;
  bool returns_value = ProductionReturnsValue(production);
  if (returns_value) {
    uint32_t w = DeclaredTypeWidth(production->return_type, ctx);
    if (w == 0 && !ProductionReturnsString(production)) w = 32;
    ret_value = MakeLogic4VecVal(arena, w, 0);
  }
  Logic4Vec* prev_slot =
      ctx.SetRsReturnSlot(returns_value ? &ret_value : nullptr);

  const auto& selected = SelectRule(*production, ctx, arena);
  auto result = co_await ExecSelectedRule(stmt, selected, ctx, arena);

  ctx.SetRsReturnSlot(prev_slot);
  ctx.PopScope();

  if (returns_value && ProductionReturnsString(production)) {
    ret_value = StripStringZeros(ret_value, arena);
  }

  RuleProductionSlot slot = SlotForAppearance(cap, call, production->name);
  if (returns_value && slot.idx != 0) {
    StoreRuleProductionValue(slot, production, ret_value, ctx, arena);
  }

  if (result == StmtResult::kReturn) co_return StmtResult::kDone;
  co_return result;
}

ExecTask ExecRandsequence(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->rs_productions.empty()) co_return StmtResult::kDone;

  std::string_view top = stmt->rs_top_production;
  if (top.empty()) top = stmt->rs_productions[0].name;

  ctx.PushScope();
  RsProductionItem top_call;
  top_call.name = top;
  auto result = co_await ExecRsProduction(stmt, top_call, ctx, arena, nullptr);
  ctx.PopScope();

  if (result == StmtResult::kBreak) co_return StmtResult::kDone;
  co_return result;
}

}  // namespace delta
