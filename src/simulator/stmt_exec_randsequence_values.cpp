#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/stmt_exec_randsequence_internal.h"

namespace delta {

const RsProduction* FindProduction(const Stmt* stmt, std::string_view name);
bool ProductionReturnsValue(const RsProduction* p);
bool ProductionReturnsString(const RsProduction* p);

static const Expr* ProductionActual(const RsProduction* production,
                                    const RsProductionItem& call,
                                    size_t index) {
  const size_t kPositional = call.args.size() - call.arg_names.size();
  if (index < kPositional) return call.args[index];
  for (size_t j = 0; j < call.arg_names.size(); ++j) {
    if (call.arg_names[j] == production->ports[index].name) {
      return call.args[kPositional + j];
    }
  }
  return nullptr;
}

std::vector<std::optional<Logic4Vec>> EvalProductionActuals(
    const RsProduction* production, const RsProductionItem& call,
    SimContext& ctx, Arena& arena) {
  std::vector<std::optional<Logic4Vec>> actuals(production->ports.size());
  for (size_t i = 0; i < production->ports.size(); ++i) {
    const Expr* actual = ProductionActual(production, call, i);
    if (actual == nullptr) continue;
    uint32_t w = DeclaredTypeWidth(production->ports[i].data_type, ctx);
    actuals[i] = EvalExpr(actual, ctx, arena, w);
  }
  return actuals;
}

void BindProductionFormals(const RsProduction* production,
                           const std::vector<std::optional<Logic4Vec>>& actuals,
                           SimContext& ctx, Arena& arena) {
  for (size_t i = 0; i < production->ports.size(); ++i) {
    const auto& port = production->ports[i];
    uint32_t w = DeclaredTypeWidth(port.data_type, ctx);
    const std::optional<Logic4Vec>& actual = actuals[i];
    Logic4Vec val;
    if (actual.has_value()) {
      val = *actual;
    } else if (port.default_value != nullptr) {
      val = EvalExpr(port.default_value, ctx, arena, w);
    } else {
      val = MakeLogic4VecVal(arena, w ? w : 32, 0);
    }
    val = ResizeToWidth(val, w, arena);
    uint32_t vw = val.width ? val.width : (w ? w : 32);
    auto* var = ctx.CreateLocalVariable(port.name, vw);
    var->value = val;
  }
}

static void CountRuleProductionItem(const Stmt* stmt,
                                    const RsProductionItem& item,
                                    RuleValueCapture& cap) {
  if (!ProductionReturnsValue(FindProduction(stmt, item.name))) return;
  cap.ordinal[&item] = ++cap.total[item.name];
}

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

static void RegisterRuleValueArrays(const Stmt* stmt,
                                    const RuleValueCapture& cap,
                                    SimContext& ctx) {
  for (const auto& [name, n] : cap.total) {
    if (n <= 1) continue;
    const auto* child = FindProduction(stmt, name);
    ArrayInfo info;
    info.lo = 1;
    info.size = static_cast<uint32_t>(n);
    uint32_t w = DeclaredTypeWidth(child->return_type, ctx);
    info.elem_type_kind = child->return_type.kind;
    info.elem_width = w ? w : (ProductionReturnsString(child) ? 0 : 32);
    ctx.RegisterLocalArray(name, info);
  }
}

RuleValueCapture BuildRuleValueCapture(const Stmt* stmt, const RsRule& selected,
                                       SimContext& ctx) {
  RuleValueCapture cap;
  for (const auto& item : selected.rand_join_items) {
    CountRuleProductionItem(stmt, item, cap);
  }
  for (const auto& prod : selected.prods) {
    CountRuleProductions(stmt, prod, cap);
  }
  RegisterRuleValueArrays(stmt, cap, ctx);
  return cap;
}

RuleValueCapture BuildStepValueCapture(const Stmt* stmt,
                                       const std::vector<const RsProd*>& steps,
                                       SimContext& ctx) {
  RuleValueCapture cap;
  for (const auto* step : steps) {
    CountRuleProductions(stmt, *step, cap);
  }
  RegisterRuleValueArrays(stmt, cap, ctx);
  return cap;
}

RuleProductionSlot SlotForAppearance(const RuleValueCapture* cap,
                                     const RsProductionItem& call,
                                     std::string_view name) {
  if (cap == nullptr) return RuleProductionSlot{name, 0, 0};
  auto ord = cap->ordinal.find(&call);
  if (ord == cap->ordinal.end()) return RuleProductionSlot{name, 0, 0};
  auto total = cap->total.find(name);
  return RuleProductionSlot{name, ord->second,
                            total == cap->total.end() ? 1 : total->second};
}

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

void StoreRuleProductionValue(const RuleProductionSlot& slot,
                              const RsProduction* child,
                              const Logic4Vec& ret_value, SimContext& ctx,
                              Arena& arena) {
  uint32_t w = DeclaredTypeWidth(child->return_type, ctx);
  if (w == 0) w = ret_value.width;
  if (w == 0 && !ProductionReturnsString(child)) w = 32;
  std::string_view created_name;
  Variable* var =
      CreateRuleProductionVariable(slot, w, ctx, arena, &created_name);
  var->value = ret_value;
  if (ProductionReturnsString(child)) ctx.RegisterStringVariable(created_name);
}

}  // namespace delta
