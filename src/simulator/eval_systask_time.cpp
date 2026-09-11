// §20.3's simulation time functions and §20.4's timescale system tasks:
// $time, $stime and $realtime, which report the current simulation time in the
// time unit of the module that invoked them; $timeunit and $timeprecision,
// which report the time unit and precision of a design element as the Table
// 20-2 base-10 order; $printtimescale, which displays both; and $timeformat,
// which sets the units, precision, suffix and minimum field width the %t
// format specifier renders a time with.
//
// What the group shares is the timescale model SimContext holds: a tick count
// kept in the design's global precision, and a per-scope TimeScale saying what
// unit and precision that scope was declared in. Every function here either
// converts between the two or reports one of them, which is why §20.3 and
// §20.4 sit together rather than with the rest of the system functions.
//
// These were in src/simulator/eval_system_func.cpp, which reached 951 lines
// against the 950 that assert-no-oversized-source-files in
// .github/workflows/deltahdl.yml warns at and the 1000 it fails at. The
// dispatcher that selects them, EvalMiscSysCall, stays there and reaches the
// four entry points below through simulator/eval_systask_internal.h.
//
// ExtractStringArg stays with the dispatcher as well: Annex D's $log takes the
// file name it opens through the same unquoting that $timeformat's
// suffix_string does, so the header declares it and this file calls across.

#include <cstdint>
#include <cstring>
#include <iostream>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "parser/ast.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
// §37.82: the VPI model reaches the $timeformat() call that set the active time
// format, so the run stands one up as the task runs.
#include "simulator/vpi.h"

namespace delta {

// §20.3.1: $time reports the current simulation time as a 64-bit integer
// expressed in the time unit of the module that invoked it. The scheduler
// keeps time in ticks of the global precision (the finest precision in the
// design), so converting to the invoking module's unit divides the tick count
// by the number of precision steps that make up one unit. Because $time has an
// integer return type, the quotient is rounded to the nearest integer; the
// design's time precision itself plays no part in that rounding.
static uint64_t CurrentTimeInModuleUnits(SimContext& ctx) {
  uint64_t ticks = ctx.CurrentTime().ticks;
  const TimeScale& scale = ctx.CurrentTimeScale();
  int unit_order = EffectiveTimeOrder(scale.unit, scale.magnitude);
  int prec_order = static_cast<int>(ctx.StepTimeUnit());
  int exp = unit_order - prec_order;  // >= 0: the unit is no finer than a tick
  if (exp <= 0) return ticks;
  uint64_t steps_per_unit = 1;
  for (int i = 0; i < exp; ++i) steps_per_unit *= 10;
  return (ticks + steps_per_unit / 2) / steps_per_unit;  // round to nearest
}

// §20.3.3: $realtime reports the current simulation time scaled to the
// invoking module's time unit just as $time does, but the result is a real
// number rather than an integer. Because the return type is real, the scaled
// value keeps its fractional part instead of being rounded to the nearest
// integer (e.g. a 16 ns time under a 10 ns unit yields 1.6, not 2).
static double CurrentTimeInModuleUnitsReal(SimContext& ctx) {
  uint64_t ticks = ctx.CurrentTime().ticks;
  const TimeScale& scale = ctx.CurrentTimeScale();
  int unit_order = EffectiveTimeOrder(scale.unit, scale.magnitude);
  int prec_order = static_cast<int>(ctx.StepTimeUnit());
  int exp = unit_order - prec_order;  // >= 0: the unit is no finer than a tick
  if (exp <= 0) return static_cast<double>(ticks);
  double steps_per_unit = 1.0;
  for (int i = 0; i < exp; ++i) steps_per_unit *= 10.0;
  return static_cast<double>(ticks) / steps_per_unit;
}

Logic4Vec EvalTimeSysCall(SimContext& ctx, Arena& arena,
                          std::string_view name) {
  if (name == "$stime") {
    // §20.3.2: $stime reports the current time scaled to the invoking module's
    // time unit just as $time does, but as an unsigned 32-bit value. When the
    // scaled time does not fit in 32 bits, only its low-order 32 bits are
    // returned; the 32-bit result width performs that truncation.
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

// Extract the design-element name an argument to $timeunit/$timeprecision
// refers to. Bare $root/$unit are modeled by the parser as argument-less
// system calls; an ordinary hierarchical reference is an identifier.
static std::string_view TimescaleArgName(const Expr* arg) {
  if (arg->kind == ExprKind::kSystemCall) return arg->callee;
  if (arg->kind == ExprKind::kIdentifier) {
    return arg->scope_prefix.empty() ? arg->text : arg->scope_prefix;
  }
  return {};
}

// §20.4.1: $timeunit and $timeprecision return the time unit or precision of a
// design element, encoded as the base-10 order from Table 20-2 (an integer in
// the range 2 to -15). With no argument the current scope is reported; an
// argument names the design element, $unit names the compilation unit, and
// $root yields the simulation time unit for both functions (see 3.14.3).
Logic4Vec EvalTimescaleQuery(const Expr* expr, SimContext& ctx, Arena& arena,
                             std::string_view name) {
  bool want_precision = (name == "$timeprecision");
  const TimeScale* scale = &ctx.CurrentTimeScale();
  bool use_sim_time_unit = false;
  if (!expr->args.empty() && expr->args[0] != nullptr) {
    std::string_view target = TimescaleArgName(expr->args[0]);
    if (target == "$root") {
      use_sim_time_unit = true;
    } else if (target == "$unit") {
      scale = &ctx.CompUnitTimeScale();
    } else if (const TimeScale* found = ctx.FindScopeTimeScale(target)) {
      scale = found;
    }
  }
  int order = 0;
  if (use_sim_time_unit) {
    order = static_cast<int>(ctx.StepTimeUnit());
  } else if (want_precision) {
    order = EffectiveTimeOrder(scale->precision, scale->prec_magnitude);
  } else {
    order = EffectiveTimeOrder(scale->unit, scale->magnitude);
  }
  auto result = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(order));
  result.is_signed = true;
  return result;
}

// Render a Table 20-2 base-10 order (in the range 2 .. -15) as the
// magnitude-and-unit text used in $printtimescale output, e.g. -7 -> "100ns",
// -12 -> "1ps", -15 -> "1fs". The SI unit comes from the nearest multiple of
// three at or below the order; the remainder selects the 1/10/100 mantissa.
static std::string TimeOrderToUnitString(int order) {
  int base = (order >= 0) ? (order / 3) * 3 : -(((-order) + 2) / 3) * 3;
  int diff = order - base;  // 0, 1, or 2
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
      break;  // -15
  }
  return std::string(mantissa) + unit;
}

// §20.4.2: assemble the line $printtimescale displays for `expr`, reading the
// timescale model in `ctx`. The output names the targeted design element and
// reports its time unit and precision in the fixed format
// "Time scale of (<name>) is <unit> / <precision>". With no argument the
// current scope is described; a named argument selects that element; the
// special $unit and $root arguments select the compilation unit and the
// simulation time unit, and in those two cases the literal "$unit"/"$root" is
// shown in place of a design-element name.
std::string BuildPrinttimescaleReport(const Expr* expr, SimContext& ctx) {
  std::string name;
  const TimeScale* scale = &ctx.CurrentTimeScale();
  bool use_sim_time_unit = false;
  if (!expr->args.empty() && expr->args[0] != nullptr) {
    std::string_view target = TimescaleArgName(expr->args[0]);
    if (target == "$root") {
      use_sim_time_unit = true;
      name = "$root";
    } else if (target == "$unit") {
      scale = &ctx.CompUnitTimeScale();
      name = "$unit";
    } else {
      name = std::string(target);
      if (const TimeScale* found = ctx.FindScopeTimeScale(target))
        scale = found;
    }
  } else {
    name = ctx.CurrentScopeName();
  }
  int unit_order = 0;
  int prec_order = 0;
  if (use_sim_time_unit) {
    // The simulation time unit and the global precision are synonymous, so
    // $root reports the same value for both fields (see 3.14.3).
    unit_order = static_cast<int>(ctx.StepTimeUnit());
    prec_order = unit_order;
  } else {
    unit_order = EffectiveTimeOrder(scale->unit, scale->magnitude);
    prec_order = EffectiveTimeOrder(scale->precision, scale->prec_magnitude);
  }
  return "Time scale of (" + name + ") is " +
         TimeOrderToUnitString(unit_order) + " / " +
         TimeOrderToUnitString(prec_order);
}

Logic4Vec EvalPrinttimescaleTask(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  std::cout << BuildPrinttimescaleReport(expr, ctx) << "\n";
  return MakeLogic4VecVal(arena, 1, 0);
}

// $timeformat (20.4.3) shall accept units_number and precision_number values
// in the Table 20-2 range from 2 to -15; out-of-range integers are rejected
// and the configured state is left untouched.
static bool TimeformatRangeOk(int64_t v) { return v <= 2 && v >= -15; }

// Evaluate one $timeformat integer field (units_number or precision_number),
// range-check it against Table 20-2, and store it into `out`. Returns false and
// emits a diagnostic naming `field` when the value is out of range, in which
// case `out` is left untouched and the caller must abort.
static bool ApplyTimeformatRangeField(const Expr* arg, SimContext& ctx,
                                      Arena& arena, const char* field,
                                      int& out) {
  auto v = static_cast<int64_t>(EvalExpr(arg, ctx, arena).ToUint64());
  // The value arrives as an unsigned 64-bit word, so widen the negative
  // 32-bit pattern back into a signed integer for the range check.
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

// Apply the two range-checked integer fields (units_number, precision_number)
// of a $timeformat call onto `spec`. Returns false when either field is out of
// the Table 20-2 range, in which case the diagnostic has been emitted and the
// caller must abort without committing the spec.
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

// Apply the optional suffix_string (arg 2) and minimum_field_width (arg 3) of a
// $timeformat call onto `spec`. A string literal suffix is taken verbatim; any
// other expression is evaluated and formatted as a string.
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
  // Bare $timeformat with no parens block leaves the configured state alone.
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);

  TimeFormatSpec spec = ctx.GetTimeFormat();
  if (!ApplyTimeformatRangeFields(expr, ctx, arena, spec)) {
    return MakeLogic4VecVal(arena, 1, 0);
  }
  ApplyTimeformatTextFields(expr, ctx, arena, spec);
  ctx.SetTimeFormat(spec);
  // §37.82: an application reaches the $timeformat() call the active format
  // came from through vpi_handle(vpiActiveTimeFormat, NULL), and detail 1 keeps
  // NULL for a run where the task has not been called - so this call is what it
  // reaches from here on.
  GetGlobalVpiContext().NoteTimeFormatCall();
  return MakeLogic4VecVal(arena, 1, 0);
}

}  // namespace delta
