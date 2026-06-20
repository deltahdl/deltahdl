#include <algorithm>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/vcd_writer.h"

namespace delta {

static bool IsMathSysCall(std::string_view n) {
  return n == "$ln" || n == "$log10" || n == "$exp" || n == "$sqrt" ||
         n == "$pow" || n == "$floor" || n == "$ceil" || n == "$sin" ||
         n == "$cos" || n == "$tan" || n == "$asin" || n == "$acos" ||
         n == "$atan" || n == "$atan2" || n == "$hypot" || n == "$sinh" ||
         n == "$cosh" || n == "$tanh" || n == "$asinh" || n == "$acosh" ||
         n == "$atanh" || n == "$dist_uniform" || n == "$dist_normal" ||
         n == "$dist_exponential" || n == "$dist_poisson" ||
         n == "$dist_chi_square" || n == "$dist_t" || n == "$dist_erlang";
}

static bool IsExtFileIOSysCall(std::string_view n) {
  return n == "$fgets" || n == "$fgetc" || n == "$fflush" || n == "$feof" ||
         n == "$ferror" || n == "$fseek" || n == "$ftell" || n == "$rewind" ||
         n == "$ungetc" || n == "$fscanf" || n == "$fread";
}

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

static Logic4Vec EvalTimeSysCall(SimContext& ctx, Arena& arena,
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
static Logic4Vec EvalTimescaleQuery(const Expr* expr, SimContext& ctx,
                                    Arena& arena, std::string_view name) {
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

static Logic4Vec EvalSystemCommand(const Expr* expr, Arena& arena) {
  int ret = 0;
  if (expr->args.empty()) {
    // §20.17.1: invoked with no string argument, $system calls the C system()
    // with the NULL string rather than executing any command.
    ret = std::system(nullptr);
  } else {
    auto text = expr->args[0]->text;
    std::string cmd;
    if (text.size() >= 2 && text.front() == '"') {
      cmd = std::string(text.substr(1, text.size() - 2));
    } else {
      cmd = std::string(text);
    }
    // §20.17.1: the argument is handed to C system() as if executed from the
    // terminal.
    ret = std::system(cmd.c_str());
  }
  // §20.17.1: as a function, $system returns the system() result with the
  // signed data type int.
  auto result = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(ret));
  result.is_signed = true;
  return result;
}

// §20.17.2: build the call-stack text reported by $stacktrace. The chain runs
// from the context that invoked $stacktrace up to the top-level process, so the
// innermost active subroutine is listed first and each enclosing caller follows
// on its own line. The exact content is implementation dependent; here it is
// the names of the subroutine frames currently on the call stack.
std::string BuildStackTraceReport(const SimContext& ctx) {
  const auto& frames = ctx.FuncNameStack();
  std::string report;
  for (auto it = frames.rbegin(); it != frames.rend(); ++it) {
    if (!report.empty()) report += '\n';
    report += std::string(*it);
  }
  return report;
}

static bool IsUtilitySysCall(std::string_view n) {
  return n == "$clog2" || n == "$bits" || n == "$unsigned" || n == "$signed" ||
         n == "$countones" || n == "$onehot" || n == "$onehot0" ||
         n == "$isunknown" || n == "$isunbounded" || n == "$cast" ||
         n == "$test$plusargs" || n == "$value$plusargs" || n == "$typename" ||
         n == "$sformatf" || n == "$itor" || n == "$rtoi" ||
         n == "$bitstoreal" || n == "$realtobits" || n == "$countbits" ||
         n == "$shortrealtobits" || n == "$bitstoshortreal";
}

static bool IsArrayQuerySysCall(std::string_view n) {
  return n == "$dimensions" || n == "$unpacked_dimensions" || n == "$left" ||
         n == "$right" || n == "$low" || n == "$high" || n == "$increment" ||
         n == "$size";
}

static bool IsVerifSysCall(std::string_view n) {
  // §16.9.4: the global clocking sampled value functions all carry the `_gclk`
  // suffix ($past_gclk, $rose_gclk, …, $changing_gclk).
  return n == "$sampled" || n == "$rose" || n == "$fell" || n == "$stable" ||
         n == "$past" || n == "$changed" || n.ends_with("_gclk") ||
         n.starts_with("$assert") || n.starts_with("$coverage") ||
         n.starts_with("$q_") || n.starts_with("$async$") ||
         n.starts_with("$sync$");
}

// §21.3.2 file-output tasks: $fdisplay, $fwrite, $fstrobe, $fmonitor and their
// b/h/o radix variants ($fdisplayb, $fwriteh, …). Returns true when `n` is one
// of those base names or a base name with a single b/h/o radix suffix.
static bool IsFileOutputTask(std::string_view n) {
  for (auto base : {"$fdisplay", "$fwrite", "$fstrobe", "$fmonitor"}) {
    if (n == base) return true;
    std::string_view base_view = base;
    if (n.size() == base_view.size() + 1 &&
        n.substr(0, base_view.size()) == base_view) {
      char c = n.back();
      if (c == 'b' || c == 'h' || c == 'o') return true;
    }
  }
  return false;
}

static bool IsIOSysCall(std::string_view n) {
  if (n == "$fopen" || n == "$fclose" || n == "$readmemh" || n == "$readmemb" ||
      n == "$writememh" || n == "$writememb" || n == "$sscanf") {
    return true;
  }
  // §D.14: $sreadmemh / $sreadmemb load a memory from string arguments.
  if (n == "$sreadmemh" || n == "$sreadmemb") return true;
  // §21.3.3: the variable-targeted output tasks share the IO syscall path
  // with their $fwrite / $fdisplay counterparts.
  if (n == "$swrite" || n == "$swriteb" || n == "$swriteh" || n == "$swriteo" ||
      n == "$sformat") {
    return true;
  }
  return IsFileOutputTask(n);
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

static Logic4Vec EvalPrinttimescaleTask(const Expr* expr, SimContext& ctx,
                                        Arena& arena) {
  std::cout << BuildPrinttimescaleReport(expr, ctx) << "\n";
  return MakeLogic4VecVal(arena, 1, 0);
}

// $timeformat (20.4.3) shall accept units_number and precision_number values
// in the Table 20-2 range from 2 to -15; out-of-range integers are rejected
// and the configured state is left untouched.
static bool TimeformatRangeOk(int64_t v) { return v <= 2 && v >= -15; }

static std::string ExtractStringArg(const Expr* arg) {
  if (!arg) return {};
  auto text = arg->text;
  if (text.size() >= 2 && text.front() == '"' && text.back() == '"') {
    return std::string(text.substr(1, text.size() - 2));
  }
  return std::string(text);
}

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
        {}, std::string("$timeformat ") + field + " out of range [2 .. -15]");
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

static Logic4Vec EvalTimeformatTask(const Expr* expr, SimContext& ctx,
                                    Arena& arena) {
  // Bare $timeformat with no parens block leaves the configured state alone.
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);

  TimeFormatSpec spec = ctx.GetTimeFormat();
  if (!ApplyTimeformatRangeFields(expr, ctx, arena, spec)) {
    return MakeLogic4VecVal(arena, 1, 0);
  }
  ApplyTimeformatTextFields(expr, ctx, arena, spec);
  ctx.SetTimeFormat(spec);
  return MakeLogic4VecVal(arena, 1, 0);
}

// Dispatch the system calls selected by a name-family classifier (math,
// utility, IO, file IO, array-query, verification) and, when none match, the
// PRNG family that consumes any remaining name. Kept separate from the
// timekeeping/output dispatch so each chain stays self-contained.
static Logic4Vec EvalClassifiedSysCall(const Expr* expr, SimContext& ctx,
                                       Arena& arena, std::string_view name) {
  if (IsMathSysCall(name)) return EvalMathSysCall(expr, ctx, arena, name);
  if (IsUtilitySysCall(name)) return EvalUtilitySysCall(expr, ctx, arena, name);
  if (IsIOSysCall(name)) return EvalIOSysCall(expr, ctx, arena, name);
  if (IsExtFileIOSysCall(name))
    return EvalFileIOSysCall(expr, ctx, arena, name);
  if (IsArrayQuerySysCall(name))
    return EvalArrayQuerySysCall(expr, ctx, arena, name);
  if (IsVerifSysCall(name)) return EvalVerifSysCall(expr, ctx, arena, name);
  return EvalPrngCall(expr, ctx, arena, name);
}

static Logic4Vec EvalMiscSysCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, std::string_view name) {
  if (name == "$time" || name == "$stime" || name == "$realtime") {
    return EvalTimeSysCall(ctx, arena, name);
  }
  if (name == "$timeunit" || name == "$timeprecision") {
    return EvalTimescaleQuery(expr, ctx, arena, name);
  }
  if (IsStrobeTask(name)) {
    return EvalDeferredPrint(expr, ctx, arena);
  }
  if (IsMonitorTask(name)) return EvalMonitor(expr, ctx, arena);
  if (name == "$monitoron" || name == "$monitoroff") {
    return EvalMonitorFlag(ctx, arena, name);
  }
  if (name == "$timeformat") return EvalTimeformatTask(expr, ctx, arena);
  if (name == "$printtimescale")
    return EvalPrinttimescaleTask(expr, ctx, arena);
  if (name == "$system") return EvalSystemCommand(expr, arena);
  // §20.17.2: called as a function, $stacktrace returns a string holding the
  // call stack of the invoking context. (The task form, which displays the
  // same information, is handled where statements execute.)
  if (name == "$stacktrace") {
    return StringToLogic4Vec(arena, BuildStackTraceReport(ctx));
  }
  if (name.starts_with("$dump")) return EvalVcdSysCall(expr, ctx, arena, name);
  return EvalClassifiedSysCall(expr, ctx, arena, name);
}

static Logic4Vec EvalSeveritySysCall(const Expr* expr, SimContext& ctx,
                                     Arena& arena, std::string_view name) {
  if (name == "$fatal") {
    ExecSeverityTask(expr, ctx, arena, "FATAL", std::cerr);
    ctx.RequestStop();
  } else if (name == "$error") {
    ExecSeverityTask(expr, ctx, arena, "ERROR", std::cerr);
  } else if (name == "$warning") {
    ExecSeverityTask(expr, ctx, arena, "WARNING", std::cout);
  } else if (name == "$info") {
    ExecSeverityTask(expr, ctx, arena, "INFO", std::cout);
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

// Annex D.11: the argument to $scope is a complete hierarchical name. Rebuild
// that name as a string from its expression form (a bare or scoped identifier,
// or a dotted member-access chain) without evaluating it, since it names a
// level of hierarchy rather than a readable object.
static std::string HierarchicalScopeName(const Expr* e) {
  if (!e) return {};
  switch (e->kind) {
    case ExprKind::kIdentifier: {
      std::string s;
      if (!e->scope_prefix.empty()) {
        s += std::string(e->scope_prefix);
        s += (e->scope_prefix == "$unit") ? "::" : ".";
      }
      s += std::string(e->text);
      return s;
    }
    case ExprKind::kMemberAccess:
      return HierarchicalScopeName(e->lhs) + "." +
             (e->rhs ? std::string(e->rhs->text) : std::string());
    default:
      return std::string(e->text);
  }
}

// Annex D.13: each entry in the $showvars variable list names a variable, or a
// bit-select or part-select of one. Because the status of every bit of a
// selected vector is displayed, a selection is reduced to the name of the
// vector it selects from; a plain reference keeps its own name. Either way the
// name is rebuilt from the expression without evaluating it.
static std::string ShowVarsVariableName(const Expr* e) {
  if (!e) return {};
  if (e->kind == ExprKind::kSelect) {
    return ShowVarsVariableName(e->base);
  }
  return HierarchicalScopeName(e);
}

// Annex D.10: $scale converts a time value held in one module into the time
// unit of the module that invokes $scale. The argument is the complete
// hierarchical name of the source value: the hierarchy above the final
// component names the source module, whose time unit applies to the raw value,
// and the final component names the value itself. The result is that value
// rescaled by the ratio of the source time unit to the invoking module's time
// unit, so a value expressed in a coarser unit grows and one expressed in a
// finer unit shrinks. A bare name carries no enclosing module of its own, so
// the invoking module's unit applies on both sides and the value passes through
// unchanged.
static Logic4Vec EvalScale(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty() || expr->args[0] == nullptr) {
    return MakeLogic4VecVal(arena, 64, 0);
  }
  const Expr* arg = expr->args[0];
  uint64_t raw = EvalExpr(arg, ctx, arena).ToUint64();

  const TimeScale& dst = ctx.CurrentTimeScale();
  const TimeScale* src = &dst;
  if (arg->kind == ExprKind::kMemberAccess) {
    std::string source_scope = HierarchicalScopeName(arg->lhs);
    if (const TimeScale* found = ctx.FindScopeTimeScale(source_scope)) {
      src = found;
    }
  }

  // EffectiveTimeOrder yields the base-10 order of each unit (Table 20-2), so
  // their difference is the power of ten relating the two units.
  int order_diff = EffectiveTimeOrder(src->unit, src->magnitude) -
                   EffectiveTimeOrder(dst.unit, dst.magnitude);
  uint64_t result = raw;
  if (order_diff > 0) {
    for (int i = 0; i < order_diff; ++i) result *= 10;
  } else if (order_diff < 0) {
    for (int i = 0; i < -order_diff; ++i) result /= 10;
  }
  return MakeLogic4VecVal(arena, 64, result);
}

// §20.2 / Table 20-1: $stop and $finish accept an optional diagnostic level
// argument (0, 1, or 2) that selects how much information accompanies the
// control action. Level 0 prints nothing; level 1 reports the simulation time
// and the controlling task (its location); level 2 additionally summarizes the
// memory and CPU time used by the run. When no argument is supplied the level
// defaults to 1.
static void EmitSimControlDiagnostic(const Expr* expr, SimContext& ctx,
                                     Arena& arena, std::string_view task,
                                     std::ostream& os) {
  int64_t level = 1;
  if (!expr->args.empty() && expr->args[0]) {
    level =
        static_cast<int64_t>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
  }
  if (level <= 0) return;
  os << task << " at time " << ctx.CurrentTime().ticks << "\n";
  if (level >= 2) {
    os << task << ": memory and CPU time statistics unavailable\n";
  }
}

// Optional $countdrivers system function (Annex D.2). It counts the drivers on
// a net so that bus contention can be identified. The net argument shall be a
// scalar net or a bit-select of a vector net; the selected bit is the one whose
// drivers are tallied. The function returns 0 when at most one driver drives
// the net and 1 otherwise (contention). When the optional output arguments are
// present they receive, in declared order, the per-state tallies of Table D.1:
// net_is_forced, number_of_01x_drivers, number_of_0_drivers,
// number_of_1_drivers, number_of_x_drivers.
// Resolve which net and which bit of it the $countdrivers net argument names. A
// bare identifier is a scalar net (bit 0); a bit-select names a vector net bit.
// `net_name` is left empty when the argument is neither form.
static void ResolveCountDriversNet(const Expr* net_arg, SimContext& ctx,
                                   Arena& arena, std::string_view& net_name,
                                   uint32_t& bit) {
  if (net_arg == nullptr) return;
  if (net_arg->kind == ExprKind::kIdentifier) {
    net_name = net_arg->text;
  } else if (net_arg->kind == ExprKind::kSelect && net_arg->base != nullptr &&
             net_arg->base->kind == ExprKind::kIdentifier &&
             net_arg->index != nullptr) {
    net_name = net_arg->base->text;
    bit =
        static_cast<uint32_t>(EvalExpr(net_arg->index, ctx, arena).ToUint64());
  }
}

// Tally the selected bit's state across every driver registered on `net`. A
// driver in the high-impedance (z) state is not actively driving and is not
// counted; the 0/1/x tallies cover the drivers that are.
static void TallyCountDriversBit(const Net* net, uint32_t bit, uint64_t& n0,
                                 uint64_t& n1, uint64_t& nx) {
  if (net == nullptr) return;
  const uint32_t kWord = bit / 64;
  const uint64_t kMask = uint64_t{1} << (bit % 64);
  for (const auto& drv : net->drivers) {
    if (kWord >= drv.nwords) continue;
    const bool kA = (drv.words[kWord].aval & kMask) != 0;
    const bool kB = (drv.words[kWord].bval & kMask) != 0;
    if (!kB && !kA)
      ++n0;
    else if (!kB && kA)
      ++n1;
    else if (kB && kA)
      ++nx;
  }
}

static Logic4Vec EvalCountDrivers(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  const Expr* net_arg = expr->args.empty() ? nullptr : expr->args[0];
  std::string_view net_name;
  uint32_t bit = 0;
  ResolveCountDriversNet(net_arg, ctx, arena, net_name, bit);

  uint64_t n0 = 0, n1 = 0, nx = 0;
  Net* net = net_name.empty() ? nullptr : ctx.FindNet(net_name);
  TallyCountDriversBit(net, bit, n0, n1, nx);
  const uint64_t kN01x = n0 + n1 + nx;

  // Write back any supplied output arguments per Table D.1, in declared order.
  const bool kForced =
      net != nullptr && net->resolved != nullptr && net->resolved->is_forced;
  const uint64_t kOuts[5] = {kForced ? 1u : 0u, kN01x, n0, n1, nx};
  for (size_t i = 1; i < expr->args.size() && i <= 5u; ++i) {
    if (expr->args[i] != nullptr) {
      PerformBlockingAssign(
          expr->args[i], MakeLogic4VecVal(arena, 32, kOuts[i - 1]), ctx, arena);
    }
  }

  // Returns 0 with no more than one driver, 1 otherwise to flag contention.
  return MakeLogic4VecVal(arena, 1, kN01x > 1 ? 1 : 0);
}

// Optional $reset family (Annex D.8). $reset tallies a reset of the tool and
// captures its reset_value argument (the second argument, after stop_value)
// so that the value can be communicated to after the reset; the other
// arguments are accepted but carry no observable state here.
static Logic4Vec EvalAnnexDReset(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  int64_t reset_value = 0;
  if (expr->args.size() > 1 && expr->args[1]) {
    reset_value =
        static_cast<int64_t>(EvalExpr(expr->args[1], ctx, arena).ToUint64());
  }
  ctx.RecordReset(reset_value);
  return MakeLogic4VecVal(arena, 1, 0);
}

// Optional $scope system task (Annex D.11). It selects a level of hierarchy
// as the interactive scope used to identify objects. Its single argument is
// the complete hierarchical name of a module, task, function, or named block;
// record that name as the new interactive scope.
static Logic4Vec EvalAnnexDScope(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  if (!expr->args.empty() && expr->args[0]) {
    ctx.SetInteractiveScope(HierarchicalScopeName(expr->args[0]));
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

// Optional $list system task (Annex D.6). It produces a listing of a module,
// task, function, or named block. With no argument the object listed is the
// current scope setting (the interactive scope established by $scope); with
// an argument, the argument is the complete hierarchical name of the specific
// scope to list. Resolve which scope is selected and record it.
static Logic4Vec EvalAnnexDList(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  std::string target = (!expr->args.empty() && expr->args[0])
                           ? HierarchicalScopeName(expr->args[0])
                           : ctx.InteractiveScope();
  ctx.RecordListing(target);
  return MakeLogic4VecVal(arena, 1, 0);
}

// Optional $showscopes system task (Annex D.12). It produces a complete list
// of the modules, tasks, functions, and named blocks defined at the current
// scope level (the interactive scope established by $scope). An optional
// integer argument widens the listing: a nonzero value lists every such
// object in or below the current hierarchical scope, while no argument or a
// zero value lists only the objects at the current scope level itself.
// Evaluate the optional argument to decide the depth and record the request.
static Logic4Vec EvalAnnexDShowScopes(const Expr* expr, SimContext& ctx,
                                      Arena& arena) {
  bool recursive = false;
  if (!expr->args.empty() && expr->args[0]) {
    recursive = EvalExpr(expr->args[0], ctx, arena).ToUint64() != 0;
  }
  ctx.RecordShowScopes(ctx.InteractiveScope(), recursive);
  return MakeLogic4VecVal(arena, 1, 0);
}

// Optional $showvars system task (Annex D.13). It produces status information
// for the reg and net variables, scalar and vector, in the current scope (the
// interactive scope established by $scope). With no argument every variable
// in that scope is reported; with a list of variables only the named ones
// are. A bit-select or part-select of a vector reports the status of all bits
// of that vector, so such a selection is reduced to the name of its
// underlying vector. Collect the requested variable names and record the
// request against the current scope.
static Logic4Vec EvalAnnexDShowVars(const Expr* expr, SimContext& ctx,
                                    Arena& arena) {
  std::vector<std::string> vars;
  for (const Expr* arg : expr->args) {
    if (arg) vars.push_back(ShowVarsVariableName(arg));
  }
  ctx.RecordShowVars(ctx.InteractiveScope(), std::move(vars));
  return MakeLogic4VecVal(arena, 1, 0);
}

// Optional $log system task (Annex D.7). The log file holds a copy of
// everything printed to standard output. An optional filename argument closes
// the current log file and starts a new one, directing subsequent output
// there; with no argument logging is simply reenabled.
static Logic4Vec EvalAnnexDLog(const Expr* expr, SimContext& ctx,
                               Arena& arena) {
  if (!expr->args.empty() && expr->args[0]) {
    ctx.SetLogFile(ExtractStringArg(expr->args[0]));
  } else {
    ctx.EnableLogging();
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

// Dispatch the optional Annex-D interactive/diagnostic tasks ($reset family,
// $scope, $list, $showscopes, $showvars, $nolog, $log). Returns true and writes
// the call's value to `out` when `name` is one of them; returns false otherwise
// so the caller continues its own dispatch. The branches and their semantics
// are exactly those of the original inline chain.
static bool TryEvalAnnexDInteractiveTask(const Expr* expr, SimContext& ctx,
                                         Arena& arena, std::string_view name,
                                         Logic4Vec& out) {
  if (name == "$reset") {
    out = EvalAnnexDReset(expr, ctx, arena);
    return true;
  }
  // $reset_count reports how many times the tool has been reset.
  if (name == "$reset_count") {
    out = MakeLogic4VecVal(arena, 32, ctx.ResetCount());
    return true;
  }
  // $reset_value returns the reset_value argument supplied to the last $reset.
  if (name == "$reset_value") {
    out = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(ctx.ResetValue()));
    return true;
  }
  if (name == "$scope") {
    out = EvalAnnexDScope(expr, ctx, arena);
    return true;
  }
  if (name == "$list") {
    out = EvalAnnexDList(expr, ctx, arena);
    return true;
  }
  if (name == "$showscopes") {
    out = EvalAnnexDShowScopes(expr, ctx, arena);
    return true;
  }
  if (name == "$showvars") {
    out = EvalAnnexDShowVars(expr, ctx, arena);
    return true;
  }
  // Optional $nolog system task (Annex D.7): disables the standard-output copy.
  if (name == "$nolog") {
    ctx.DisableLogging();
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (name == "$log") {
    out = EvalAnnexDLog(expr, ctx, arena);
    return true;
  }
  return false;
}

Logic4Vec EvalSystemCall(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto name = expr->callee;

  // §20.16.1: a PLA modeling system task evaluates the array and drives its
  // output terms; it produces no value of its own.
  if (TryEvalPlaSystemTask(expr, ctx, arena)) {
    return MakeLogic4VecVal(arena, 1, 0);
  }

  if (IsDisplayOrWriteTask(name)) {
    ExecDisplayWrite(expr, ctx, arena);
    return MakeLogic4VecVal(arena, 1, 0);
  }
  // §20.2: $stop suspends the run and $finish ends it, returning control to the
  // host; both honor the Table 20-1 diagnostic level before halting.
  if (name == "$finish" || name == "$stop") {
    EmitSimControlDiagnostic(expr, ctx, arena, name, std::cout);
    ctx.RequestStop();
    return MakeLogic4VecVal(arena, 1, 0);
  }
  // Optional $countdrivers function (Annex D.2).
  if (name == "$countdrivers") {
    return EvalCountDrivers(expr, ctx, arena);
  }
  Logic4Vec annex_d_result;
  if (TryEvalAnnexDInteractiveTask(expr, ctx, arena, name, annex_d_result)) {
    return annex_d_result;
  }
  // Optional $scale function (Annex D.10). It reads the time value named by a
  // hierarchical reference and converts it from the time unit of the module
  // that holds it to the time unit of the module that invokes $scale.
  if (name == "$scale") {
    return EvalScale(expr, ctx, arena);
  }
  if (name == "$exit") {
    auto* cur = ctx.CurrentProcess();
    if (cur && cur->program_block_id != 0) {
      ctx.ExitProgramBlock(cur->program_block_id);
    }
    return MakeLogic4VecVal(arena, 1, 0);
  }
  if (name == "$fatal" || name == "$error" || name == "$warning" ||
      name == "$info") {
    return EvalSeveritySysCall(expr, ctx, arena, name);
  }
  return EvalMiscSysCall(expr, ctx, arena, name);
}

}  // namespace delta
