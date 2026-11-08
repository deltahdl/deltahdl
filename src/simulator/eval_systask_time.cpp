#include <cstdint>
#include <cstring>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/scope.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"

namespace delta {

static uint64_t CurrentTimeInModuleUnits(SimContext& ctx) {
  uint64_t ticks = ctx.CurrentTime().ticks;
  const TimeScale& scale = ActiveInstanceTimeScale(ctx);
  int unit_order = EffectiveTimeOrder(scale.unit, scale.magnitude);
  int prec_order = static_cast<int>(ctx.StepTimeUnit());
  int exp = unit_order - prec_order;
  if (exp <= 0) return ticks;
  uint64_t steps_per_unit = 1;
  for (int i = 0; i < exp; ++i) steps_per_unit *= 10;
  return (ticks + steps_per_unit / 2) / steps_per_unit;
}

static double CurrentTimeInModuleUnitsReal(SimContext& ctx) {
  uint64_t ticks = ctx.CurrentTime().ticks;
  const TimeScale& scale = ActiveInstanceTimeScale(ctx);
  int unit_order = EffectiveTimeOrder(scale.unit, scale.magnitude);
  int prec_order = static_cast<int>(ctx.StepTimeUnit());
  int exp = unit_order - prec_order;
  if (exp <= 0) return static_cast<double>(ticks);
  double steps_per_unit = 1.0;
  for (int i = 0; i < exp; ++i) steps_per_unit *= 10.0;
  return static_cast<double>(ticks) / steps_per_unit;
}

Logic4Vec EvalTimeSysCall(SimContext& ctx, Arena& arena,
                          std::string_view name) {
  if (name == "$stime") {
    return MakeLogic4VecVal(arena, 32, CurrentTimeInModuleUnits(ctx));
  }
  if (name == "$realtime") {
    double scaled = CurrentTimeInModuleUnitsReal(ctx);
    uint64_t bits = 0;
    std::memcpy(&bits, &scaled, sizeof(double));
    auto result = MakeLogic4VecVal(arena, 64, bits);
    result.is_real = true;
    return result;
  }
  if (name == "$time") {
    return MakeLogic4VecVal(arena, 64, CurrentTimeInModuleUnits(ctx));
  }
  return MakeLogic4VecVal(arena, 64, ctx.CurrentTime().ticks);
}

static std::string TimescaleArgName(const Expr* arg) {
  if (arg->kind == ExprKind::kSystemCall) return std::string(arg->callee);
  if (arg->kind == ExprKind::kMemberAccess) return FlattenHierPath(arg);
  if (arg->kind == ExprKind::kIdentifier) {
    return std::string(arg->scope_prefix.empty() ? arg->text
                                                 : arg->scope_prefix);
  }
  return {};
}

static const TimeScale* FindNamedTimeScale(const SimContext& ctx,
                                           const std::string& target) {
  if (const TimeScale* found = ctx.FindScopeTimeScale(target)) return found;
  return ctx.FindScopeTimeScale(target + "::");
}

Logic4Vec EvalTimescaleQuery(const Expr* expr, SimContext& ctx, Arena& arena,
                             std::string_view name) {
  bool want_precision = (name == "$timeprecision");
  const TimeScale* scale = &ActiveInstanceTimeScale(ctx);
  if (!expr->args.empty() && expr->args[0] != nullptr) {
    std::string target = TimescaleArgName(expr->args[0]);
    if (target == "$unit") {
      scale = &ctx.CompUnitTimeScale();
    } else if (const TimeScale* found = FindNamedTimeScale(ctx, target)) {
      scale = found;
    }
  }
  int order = 0;
  if (want_precision) {
    order = EffectiveTimeOrder(scale->precision, scale->prec_magnitude);
  } else {
    order = EffectiveTimeOrder(scale->unit, scale->magnitude);
  }
  auto result = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(order));
  result.is_signed = true;
  return result;
}

static std::string TimeOrderToUnitString(int order) {
  int base = (order >= 0) ? (order / 3) * 3 : -(((-order) + 2) / 3) * 3;
  int diff = order - base;
  const char* mantissa = diff == 2 ? "100" : (diff == 1 ? "10" : "1");
  const char* unit = nullptr;
  switch (base) {
    case 0:
      unit = "s";
      break;
    case -3:
      unit = "ms";
      break;
    case -6:
      unit = "us";
      break;
    case -9:
      unit = "ns";
      break;
    case -12:
      unit = "ps";
      break;
    default:
      unit = "fs";
      break;
  }
  return std::string(mantissa) + unit;
}

const TimeScale& ActiveInstanceTimeScale(const SimContext& ctx) {
  if (const Scope* frame = ctx.PackageFrame()) {
    if (frame->package == "$unit") return ctx.CompUnitTimeScale();
    std::string key(frame->package);
    key += "::";
    if (const TimeScale* found = ctx.FindScopeTimeScale(key)) return *found;
  }
  std::string prefix = ctx.ActiveInstancePrefix();
  if (!prefix.empty()) prefix.pop_back();
  if (const TimeScale* found = ctx.FindScopeTimeScale(prefix)) return *found;
  return ctx.CurrentTimeScale();
}

std::string BuildPrinttimescaleReport(const Expr* expr, SimContext& ctx) {
  std::string name;
  const TimeScale* scale = &ActiveInstanceTimeScale(ctx);
  if (!expr->args.empty() && expr->args[0] != nullptr) {
    std::string target = TimescaleArgName(expr->args[0]);
    if (target == "$unit") {
      scale = &ctx.CompUnitTimeScale();
      name = "$unit";
    } else {
      name = target;
      if (const TimeScale* found = FindNamedTimeScale(ctx, target))
        scale = found;
    }
  } else {
    name = ctx.CurrentScopeName();
    std::string prefix = ctx.ActiveInstancePrefix();
    if (!prefix.empty()) {
      prefix.pop_back();
      name += "." + prefix;
    }
  }
  int unit_order = EffectiveTimeOrder(scale->unit, scale->magnitude);
  int prec_order = EffectiveTimeOrder(scale->precision, scale->prec_magnitude);
  return "Time scale of (" + name + ") is " +
         TimeOrderToUnitString(unit_order) + " / " +
         TimeOrderToUnitString(prec_order);
}

Logic4Vec EvalPrinttimescaleTask(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  ctx.Out() << BuildPrinttimescaleReport(expr, ctx) << "\n";
  return MakeLogic4VecVal(arena, 1, 0);
}

static bool TimeformatRangeOk(int64_t v) { return v <= 2 && v >= -15; }

static bool ApplyTimeformatRangeField(const Expr* arg, SimContext& ctx,
                                      Arena& arena, const char* field,
                                      int& out) {
  auto v = static_cast<int64_t>(EvalExpr(arg, ctx, arena).ToUint64());
  auto field_value = static_cast<int32_t>(v);
  if (!TimeformatRangeOk(field_value)) {
    ctx.GetDiag().Error(
        arg->range.start,
        std::string("$timeformat ") + field + " out of range [2 .. -15]",
        Subclause("20.4.3"));
    return false;
  }
  out = field_value;
  return true;
}

static bool ApplyTimeformatRangeFields(const Expr* expr, SimContext& ctx,
                                       Arena& arena, TimeFormatSpec& spec) {
  if (expr->args.size() >= 1 && expr->args[0]) {
    if (!ApplyTimeformatRangeField(expr->args[0], ctx, arena, "units_number",
                                   spec.units_number)) {
      return false;
    }
  }
  if (expr->args.size() >= 2 && expr->args[1]) {
    if (!ApplyTimeformatRangeField(expr->args[1], ctx, arena,
                                   "precision_number", spec.precision_number)) {
      return false;
    }
  }
  return true;
}

static void ApplyTimeformatTextFields(const Expr* expr, SimContext& ctx,
                                      Arena& arena, TimeFormatSpec& spec) {
  if (expr->args.size() >= 3 && expr->args[2]) {
    if (expr->args[2]->kind == ExprKind::kStringLiteral) {
      spec.suffix_string = ExtractStringArg(expr->args[2]);
    } else {
      spec.suffix_string =
          FormatValueAsString(EvalExpr(expr->args[2], ctx, arena));
    }
  }
  if (expr->args.size() >= 4 && expr->args[3]) {
    auto v =
        static_cast<int64_t>(EvalExpr(expr->args[3], ctx, arena).ToUint64());
    spec.minimum_field_width = static_cast<int>(v);
  }
}

Logic4Vec EvalTimeformatTask(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);

  TimeFormatSpec spec = ctx.GetTimeFormat();
  if (!ApplyTimeformatRangeFields(expr, ctx, arena, spec)) {
    return MakeLogic4VecVal(arena, 1, 0);
  }
  ApplyTimeformatTextFields(expr, ctx, arena, spec);
  ctx.SetTimeFormat(spec);
  GetGlobalVpiContext().NoteTimeFormatCall(expr, ctx);
  return MakeLogic4VecVal(arena, 1, 0);
}

}  // namespace delta
