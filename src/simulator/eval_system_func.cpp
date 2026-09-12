#include <cstdlib>
#include <cstring>
#include <iostream>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/global_clocking_sampled_value.h"
#include "elaborator/type_eval.h"
#include "parser/assertion_control_task.h"
#include "parser/ast.h"
#include "simulator/coverage.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/process.h"
#include "simulator/sdf_parser.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/vcd_writer.h"
#include "simulator/vpi_context.h"

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

// The verification system functions and tasks EvalVerifSysCall answers, named
// one by one out of the clauses that define them: §20.12 Syntax 20-13 for the
// six sampled value functions and, through IsGlobalClockingSampledFunction, the
// ten global clocking functions §16.9.4 describes; §20.11 Syntax 20-12 for the
// ten assertion control tasks, through the parser's own predicate over them;
// §20.13 for the five coverage functions; §20.15 for the five stochastic queue
// tasks.
//
// A prefix or a suffix stood for four of those lists and claimed a misspelling
// with them -- $assertofff, $coverage_gett, $q_ad, $risen_gclk -- which
// EvalVerifSysCall then answered with a zero. A name no classifier claims is
// reported under §20.1 instead, and a misspelling is what that report is for.
//
// The §20.16 PLA names are gone from here with the $async$/$sync$ prefixes that
// held them: ClassifyPlaTask generates exactly the sixteen of Table 20-12 and
// TryEvalPlaSystemTask consults it ahead of every other classifier, so a
// well-formed PLA name never reaches this point and a malformed one is not a
// name of the language.
static bool IsVerifSysCall(std::string_view n) {
  return n == "$sampled" || n == "$rose" || n == "$fell" || n == "$stable" ||
         n == "$past" || n == "$changed" ||
         IsGlobalClockingSampledFunction(n) || IsAssertionControlTaskName(n) ||
         n == "$coverage_control" || n == "$coverage_get_max" ||
         n == "$coverage_get" || n == "$coverage_merge" ||
         n == "$coverage_save" || n == "$q_initialize" || n == "$q_add" ||
         n == "$q_remove" || n == "$q_full" || n == "$q_exam";
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

std::string ExtractStringArg(const Expr* arg) {
  if (!arg) return {};
  auto text = arg->text;
  if (text.size() >= 2 && text.front() == '"' && text.back() == '"') {
    return std::string(text.substr(1, text.size() - 2));
  }
  return std::string(text);
}

// §20.1 catalogues the system tasks and system functions SystemVerilog has,
// each under the subclause that defines it, and states that "Clause 21
// presents additional system tasks and system functions that are specific to
// I/O operations". A name no classifier claimed is one this tool can carry out
// no part of, whether it is a misspelling, a task of the standard not
// implemented here, or a name the standard has never had. The three are not
// told apart, which would take the standard's whole catalogue; what they share
// is that the call does nothing, and that is what is said.
//
// A value is still returned, because the caller is an expression evaluator and
// the run carries on to whatever else it can report. What changed is that the
// value is no longer the only thing produced.
// Annex D.1 lists the system tasks and system functions Annex D describes,
// "for informative purposes only and ... not part of this standard", which
// "may not be available in all implementations", each under the subclause
// that describes it. The subclause of a name D.1 lists, or empty for a name
// it does not.
static std::string_view AnnexDSubclauseOf(std::string_view name) {
  struct AnnexDTask {
    std::string_view name;
    std::string_view subclause;
  };
  static constexpr AnnexDTask kAnnexDTasks[] = {
      {"$countdrivers", "D.2"}, {"$getpattern", "D.3"},  {"$input", "D.4"},
      {"$key", "D.5"},          {"$nokey", "D.5"},       {"$list", "D.6"},
      {"$log", "D.7"},          {"$nolog", "D.7"},       {"$reset", "D.8"},
      {"$reset_count", "D.8"},  {"$reset_value", "D.8"}, {"$incsave", "D.9"},
      {"$restart", "D.9"},      {"$save", "D.9"},        {"$scale", "D.10"},
      {"$scope", "D.11"},       {"$showscopes", "D.12"}, {"$showvars", "D.13"},
      {"$sreadmemb", "D.14"},   {"$sreadmemh", "D.14"},
  };
  for (const auto& task : kAnnexDTasks) {
    if (task.name == name) return task.subclause;
  }
  return {};
}

static Logic4Vec ReportUnknownSysCall(const Expr* expr, SimContext& ctx,
                                      Arena& arena, std::string_view name) {
  // A name D.1 lists that no classifier claimed is an optional task or
  // function this implementation is one of those without, which D.1 allows,
  // and the report says which annex subclause describes it rather than that
  // it is no system task at all.
  std::string_view annex_d = AnnexDSubclauseOf(name);
  if (!annex_d.empty()) {
    ctx.GetDiag().Error(
        expr->range.start,
        std::string(name) + " is the optional system task or system function " +
            std::string(annex_d) +
            " describes, which Annex D.1 has \"may not be available in all "
            "implementations\"; this implementation is one without it",
        Subclause("D.1"));
    return MakeLogic4VecVal(arena, 1, 0);
  }
  ctx.GetDiag().Error(expr->range.start,
                      std::string(name) +
                          " is not a system task or system function this tool "
                          "implements",
                      Subclause("20.1"));
  return MakeLogic4VecVal(arena, 1, 0);
}

// Dispatch the system calls selected by a name-family classifier (math,
// utility, IO, file IO, array-query, verification, PRNG), and report a name
// none of them claims. Kept separate from the timekeeping/output dispatch so
// each chain stays self-contained.
//
// EvalPrngCall stood at the end without a predicate of its own, answering
// every name it did not match with a one-bit zero, so the chain ran out
// silently rather than running out at all. IsPrngSysCall is what lets it
// decline, and declining is what makes the line below reachable.
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
  if (IsPrngSysCall(name)) return EvalPrngCall(expr, ctx, arena, name);
  return ReportUnknownSysCall(expr, ctx, arena, name);
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
  if (IsVcdSysCall(name)) return EvalVcdSysCall(expr, ctx, arena, name);
  // §32.9: $sdf_annotate reads timing data out of an SDF file and into the
  // region of the design its module_instance operand names. It produces no
  // value of its own.
  if (name == "$sdf_annotate") {
    EvalSdfAnnotateTask(expr, ctx, arena);
    return MakeLogic4VecVal(arena, 1, 0);
  }
  return EvalClassifiedSysCall(expr, ctx, arena, name);
}

// §20.2 / Table 20-1: emit the banner that $finish and $stop print before
// halting, at the reporting level given by their first argument. Level 0 emits
// nothing, level 1 reports the current time, and level 2 additionally reports
// resource statistics.
static void EmitFinishDiagnostic(SimContext& ctx, std::string_view task,
                                 int64_t level, std::ostream& os) {
  if (level <= 0) return;
  os << task << " at time " << ctx.CurrentTime().ticks << "\n";
  if (level >= 2) {
    os << task << ": memory and CPU time statistics unavailable\n";
  }
}

static Logic4Vec EvalSeveritySysCall(const Expr* expr, SimContext& ctx,
                                     Arena& arena, std::string_view name) {
  if (name == "$fatal") {
    ExecSeverityTask(expr, ctx, arena, "FATAL", std::cerr);
    // §20.10: calling $fatal produces an implicit $finish. Its optional first
    // argument is a finish_number consistent with $finish's argument (§20.2),
    // which selects how much diagnostic information the tool reports before it
    // halts. A leading string argument means no finish_number was supplied, so
    // the default reporting level of 1 applies.
    int64_t level = 1;
    if (!expr->args.empty() && expr->args[0] &&
        expr->args[0]->kind != ExprKind::kStringLiteral) {
      level =
          static_cast<int64_t>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
    }
    EmitFinishDiagnostic(ctx, "$finish", level, std::cout);
    ctx.RequestFinish();
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
  EmitFinishDiagnostic(ctx, task, level, os);
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
  // Table D.1's net_is_forced is asked of the bit the net argument names, and
  // §10.6.2 lets a force name "a constant bit-select of a vector net": a force
  // on bus[3] holds bit 3 and no other, so bus[7] reports 0 for it. Reading the
  // flag alone answered 1 for every bit of the net.
  const bool kForced = net != nullptr && net->resolved != nullptr &&
                       net->resolved->BitIsForced(bit);
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

// §19.9: the predefined coverage system tasks and system functions. They act on
// the run's live coverage database (SimContext::CoverageData). $get_coverage
// returns the overall coverage of all covergroup types as a real in 0..100;
// $set_coverage_db_name records the database file name; $load_coverage_db loads
// cumulative coverage from the named file. Returns false for any other name so
// the caller keeps dispatching.
static bool TryEvalCoverageSysCall(const Expr* expr, SimContext& ctx,
                                   Arena& arena, std::string_view name,
                                   Logic4Vec& out) {
  if (name == "$get_coverage") {
    double cov = ctx.CoverageData().GetGlobalCoverage();
    uint64_t bits = 0;
    std::memcpy(&bits, &cov, sizeof(double));
    out = MakeLogic4VecVal(arena, 64, bits);
    out.is_real = true;
    return true;
  }
  if (name == "$set_coverage_db_name") {
    if (!expr->args.empty() && expr->args[0] != nullptr) {
      ctx.CoverageData().SetCoverageDbName(
          EvalStringArg(expr->args[0], ctx, arena));
    }
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (name == "$load_coverage_db") {
    if (!expr->args.empty() && expr->args[0] != nullptr) {
      ctx.CoverageData().LoadCoverageDbFile(
          EvalStringArg(expr->args[0], ctx, arena));
    }
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  return false;
}

// What a registered PLI application makes of a system call written in an
// expression, and whether the registry claimed the name at all. Answers both
// halves through `out` so that the evaluator below asks the registry once,
// where it asked once before §36.5's report was owed as well.
//
// §36.5: a user-defined system task "can be used in the same places a
// SystemVerilog void function can be used", and §13.4.1 has exactly one such
// place -- "function calls may be used as expressions unless of type void,
// which are statements". The caller is the other position, so a task named
// there is a task standing where a value is wanted, and the clause's own
// reason is what is reported: a task "does not return any value". The
// statement executor calls the application instead (TryExecSystemCallTask),
// which is why nothing reaching here is the task's one legal position.
static bool TryEvalRegisteredSystf(const Expr* expr, SimContext& ctx,
                                   Arena& arena, std::string_view name,
                                   Logic4Vec& out) {
  if (SystemCallNamesARegisteredTask(expr)) {
    ctx.GetDiag().Error(
        expr->range.start,
        std::string(name) +
            " is a user-defined system task and returns no value, so it "
            "cannot be used as an expression",
        Subclause("36.5"));
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }

  // §36.4: `expr` is the call site, so the task/function arguments it wrote are
  // what the application reads through §37.42's vpiArgument iteration. They are
  // not handed to the application as C arguments -- "the task/function
  // arguments are not passed to the PLI application" -- and the calltf's own
  // parameter stays its registered user_data.
  return GetGlobalVpiContext().CallRegisteredSystf(std::string(name).c_str(),
                                                   expr, ctx, out, arena);
}

Logic4Vec EvalSystemCall(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto name = expr->callee;

  // §36.3.2: "If a user-provided PLI application is associated with the same
  // name as a built-in system task or system function (using the PLI
  // mechanism), the user-provided C application shall override the built-in
  // system task or system function, replacing its functionality", the clause's
  // own example being an application registered as $random. The registry is
  // therefore asked ahead of everything below rather than after it, and
  // §38.37.1 has the application's calltf called "each time the system task or
  // system function is invoked during simulation execution", which is here.
  //
  // A name no registration claims falls through to the built-ins, and past them
  // to §20.1's report. §36.3.2's one exception needs nothing of this dispatch:
  // "SystemVerilog timing checks, such as $setup, are not system tasks and
  // cannot be overridden", and a timing check reaches the specify machinery
  // rather than this evaluator.
  Logic4Vec systf_result;
  if (TryEvalRegisteredSystf(expr, ctx, arena, name, systf_result)) {
    return systf_result;
  }

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
    ctx.RequestFinish();
    return MakeLogic4VecVal(arena, 1, 0);
  }
  // Optional $countdrivers function (Annex D.2).
  if (name == "$countdrivers") {
    return EvalCountDrivers(expr, ctx, arena);
  }
  Logic4Vec coverage_result;
  if (TryEvalCoverageSysCall(expr, ctx, arena, name, coverage_result)) {
    return coverage_result;
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
