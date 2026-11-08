#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "elaborator/global_clocking_sampled_value.h"
#include "elaborator/type_eval.h"
#include "parser/assertion_control_task.h"
#include "parser/ast_expr.h"
#include "simulator/coverage.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/process.h"
#include "simulator/sdf_parser.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/vcd_writer.h"
#include "simulator/vpi_assertion_cb.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"

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
    ret = std::system(nullptr);
  } else {
    auto text = expr->args[0]->text;
    std::string cmd;
    if (text.size() >= 2 && text.front() == '"') {
      cmd = std::string(text.substr(1, text.size() - 2));
    } else {
      cmd = std::string(text);
    }
    ret = std::system(cmd.c_str());
  }
  auto result = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(ret));
  result.is_signed = true;
  return result;
}

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
  return n == "$sampled" || n == "$rose" || n == "$fell" || n == "$stable" ||
         n == "$past" || n == "$changed" ||
         IsGlobalClockingSampledFunction(n) || IsAssertionControlTaskName(n) ||
         n == "$coverage_control" || n == "$coverage_get_max" ||
         n == "$coverage_get" || n == "$coverage_merge" ||
         n == "$coverage_save" || n == "$q_initialize" || n == "$q_add" ||
         n == "$q_remove" || n == "$q_full" || n == "$q_exam";
}

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
  if (n == "$sreadmemh" || n == "$sreadmemb") return true;
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
  std::string_view annex_d = AnnexDSubclauseOf(name);
  if (!annex_d.empty()) {
    ctx.GetDiag().Error(
        expr->range.start,
        std::string(name) + " is the optional system task or system function " +
            std::string(annex_d) +
            " describes, which Annex D.1 allows an implementation to be "
            "without; this implementation is one without it",
        Subclause("D.1"));
    return MakeLogic4VecVal(arena, 1, 0);
  }
  std::string unresolved(name);
  GetGlobalVpiContext().DispatchCallbacks(kCbUnresolvedSystf, nullptr,
                                          unresolved.data());
  ctx.GetDiag().Error(expr->range.start,
                      std::string(name) +
                          " is not a system task or system function this tool "
                          "implements",
                      Subclause("20.1"));
  return MakeLogic4VecVal(arena, 1, 0);
}

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
  if (name == "$stacktrace") {
    return StringToLogic4Vec(arena, BuildStackTraceReport(ctx));
  }
  if (IsVcdSysCall(name)) return EvalVcdSysCall(expr, ctx, arena, name);
  if (name == "$sdf_annotate") {
    EvalSdfAnnotateTask(expr, ctx, arena);
    return MakeLogic4VecVal(arena, 1, 0);
  }
  return EvalClassifiedSysCall(expr, ctx, arena, name);
}

void EmitFinishDiagnostic(SimContext& ctx, std::string_view task, int64_t level,
                          std::ostream& os) {
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
    int64_t level = 1;
    if (!expr->args.empty() && expr->args[0] &&
        expr->args[0]->kind != ExprKind::kStringLiteral) {
      level =
          static_cast<int64_t>(EvalExpr(expr->args[0], ctx, arena).ToUint64());
    }
    EmitFinishDiagnostic(ctx, "$finish", level, ctx.Out());
    ctx.RequestFinish();
  } else if (name == "$error") {
    ExecSeverityTask(expr, ctx, arena, "ERROR", std::cerr);
  } else if (name == "$warning") {
    ExecSeverityTask(expr, ctx, arena, "WARNING", ctx.Out());
  } else if (name == "$info") {
    ExecSeverityTask(expr, ctx, arena, "INFO", ctx.Out());
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

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

static std::string ShowVarsVariableName(const Expr* e) {
  if (!e) return {};
  if (e->kind == ExprKind::kSelect) {
    return ShowVarsVariableName(e->base);
  }
  return HierarchicalScopeName(e);
}

static Logic4Vec EvalScale(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (expr->args.empty() || expr->args[0] == nullptr) {
    return MakeLogic4VecVal(arena, 64, 0);
  }
  const Expr* arg = expr->args[0];
  uint64_t raw = EvalExpr(arg, ctx, arena).ToUint64();

  const TimeScale& dst = ActiveInstanceTimeScale(ctx);
  const TimeScale* src = &dst;
  if (arg->kind == ExprKind::kMemberAccess) {
    std::string source_scope = HierarchicalScopeName(arg->lhs);
    if (const TimeScale* found = ctx.FindScopeTimeScale(source_scope)) {
      src = found;
    }
  }

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

static void TallyCountDriversBit(const Net* net, uint32_t bit, uint64_t& n0,
                                 uint64_t& n1, uint64_t& nx) {
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

static bool CheckCountDriversNet(const Expr* expr, const Expr* net_arg,
                                 const Net* net, SimContext& ctx) {
  std::string_view fault;
  if (net == nullptr) {
    fault = "names no net";
  } else if (net_arg->kind == ExprKind::kIdentifier &&
             net->resolved->value.width > 1) {
    fault = "names a vector net whole and no bit-select of it";
  }
  if (fault.empty()) return true;
  ctx.GetDiag().Error(expr->range.start,
                      "$countdrivers takes a scalar net or a bit-select of a "
                      "vector net, and its net argument " +
                          std::string(fault),
                      Subclause("D.2"));
  return false;
}

static Logic4Vec EvalCountDrivers(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  const Expr* net_arg = expr->args.empty() ? nullptr : expr->args[0];
  std::string_view net_name;
  uint32_t bit = 0;
  ResolveCountDriversNet(net_arg, ctx, arena, net_name, bit);

  Net* net = net_name.empty() ? nullptr : ctx.FindNet(net_name);
  if (!CheckCountDriversNet(expr, net_arg, net, ctx)) {
    return MakeLogic4VecVal(arena, 1, 0);
  }
  uint64_t n0 = 0, n1 = 0, nx = 0;
  TallyCountDriversBit(net, bit, n0, n1, nx);
  const uint64_t kN01x = n0 + n1 + nx;

  const bool kForced = net->resolved->BitIsForced(bit);
  const uint64_t kOuts[5] = {kForced ? 1u : 0u, kN01x, n0, n1, nx};
  for (size_t i = 1; i < expr->args.size() && i <= 5u; ++i) {
    if (expr->args[i] != nullptr) {
      PerformBlockingAssign(
          expr->args[i], MakeLogic4VecVal(arena, 32, kOuts[i - 1]), ctx, arena);
    }
  }

  return MakeLogic4VecVal(arena, 1, kN01x > 1 ? 1 : 0);
}

static Logic4Vec EvalGetpattern(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  if (expr->args.empty()) return MakeLogic4VecVal(arena, 1, 0);
  return EvalExpr(expr->args[0], ctx, arena);
}

static Logic4Vec EvalAnnexDScope(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  if (!expr->args.empty() && expr->args[0]) {
    std::string name = HierarchicalScopeName(expr->args[0]);
    if (ctx.IsHierarchicalScope(name)) {
      ctx.SetInteractiveScope(name);
      VpiContext& vpi = GetGlobalVpiContext();
      if (VpiHandle found = vpi.HandleByName(name.c_str(), nullptr)) {
        vpi.NoteInteractiveScope(VpiLabelledAssertionsBeginOr(found));
      }
    } else {
      ctx.GetDiag().Error(
          expr->args[0]->range.start,
          "$scope takes the complete hierarchical name of a module, task, "
          "function, or named block, and '" +
              name + "' is none",
          Subclause("D.11"));
    }
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalAnnexDList(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  if (expr->args.empty() || !expr->args[0]) {
    ctx.RecordListing(ctx.InteractiveScope());
    return MakeLogic4VecVal(arena, 1, 0);
  }
  std::string name = HierarchicalScopeName(expr->args[0]);
  if (ctx.IsHierarchicalScope(name)) {
    ctx.RecordListing(name);
  } else {
    ctx.GetDiag().Error(
        expr->args[0]->range.start,
        "$list takes the complete hierarchical name of a module, task, "
        "function, or named block, and '" +
            name + "' is none",
        Subclause("D.6"));
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalAnnexDShowScopes(const Expr* expr, SimContext& ctx,
                                      Arena& arena) {
  bool recursive = false;
  if (!expr->args.empty() && expr->args[0]) {
    recursive = EvalExpr(expr->args[0], ctx, arena).ToUint64() != 0;
  }
  const std::string& scope = ctx.InteractiveScope();
  for (const std::string& name :
       ctx.HierarchicalScopesUnder(scope, recursive)) {
    ctx.Out() << name << "\n";
  }
  ctx.RecordShowScopes(scope, recursive);
  return MakeLogic4VecVal(arena, 1, 0);
}

static void ShowVariableStatus(std::string_view name, const std::string& key,
                               SimContext& ctx) {
  const Variable* var = ctx.FindVariable(key);
  ctx.Out() << name << " = ";
  if (var == nullptr) {
    ctx.Out() << "<no such variable>\n";
    return;
  }
  ctx.Out() << FormatArg(var->value, 'b') << "\n";
}

static Logic4Vec EvalAnnexDShowVars(const Expr* expr, SimContext& ctx,
                                    Arena& arena) {
  std::vector<std::string> vars;
  for (const Expr* arg : expr->args) {
    if (arg) vars.push_back(ShowVarsVariableName(arg));
  }
  const std::string& scope = ctx.InteractiveScope();
  const ScopeVariableSet* declared = ctx.ScopeVariables(scope);
  std::string prefix;
  if (declared != nullptr) prefix = "$root." + declared->prefix;
  if (vars.empty() && declared != nullptr) {
    for (const std::string& name : declared->names) {
      ShowVariableStatus(name, prefix + name, ctx);
    }
  }
  for (const std::string& name : vars) {
    ShowVariableStatus(name, prefix + name, ctx);
  }
  ctx.RecordShowVars(scope, std::move(vars));
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalAnnexDLog(const Expr* expr, SimContext& ctx,
                               Arena& arena) {
  if (!expr->args.empty() && expr->args[0]) {
    ctx.Log().Open(ExtractStringArg(expr->args[0]));
  } else {
    ctx.Log().Enable();
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

static bool TryEvalAnnexDInteractiveTask(const Expr* expr, SimContext& ctx,
                                         Arena& arena, std::string_view name,
                                         Logic4Vec& out) {
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
  if (name == "$nolog") {
    ctx.Log().Disable();
    out = MakeLogic4VecVal(arena, 1, 0);
    return true;
  }
  if (name == "$log") {
    out = EvalAnnexDLog(expr, ctx, arena);
    return true;
  }
  return false;
}

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

  return GetGlobalVpiContext().CallRegisteredSystf(std::string(name).c_str(),
                                                   expr, ctx, out, arena);
}

static bool TryEvalAnnexDFunction(const Expr* expr, SimContext& ctx,
                                  Arena& arena, std::string_view name,
                                  Logic4Vec& result) {
  if (name == "$countdrivers") {
    result = EvalCountDrivers(expr, ctx, arena);
  } else if (name == "$getpattern") {
    result = EvalGetpattern(expr, ctx, arena);
  } else if (name == "$scale") {
    result = EvalScale(expr, ctx, arena);
  } else {
    return false;
  }
  return true;
}

Logic4Vec EvalSystemCall(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto name = expr->callee;

  Logic4Vec systf_result;
  if (TryEvalRegisteredSystf(expr, ctx, arena, name, systf_result)) {
    return systf_result;
  }

  if (TryEvalPlaSystemTask(expr, ctx, arena)) {
    return MakeLogic4VecVal(arena, 1, 0);
  }

  if (IsDisplayOrWriteTask(name)) {
    ExecDisplayWrite(expr, ctx, arena);
    return MakeLogic4VecVal(arena, 1, 0);
  }
  if (name == "$finish" || name == "$stop") {
    EmitSimControlDiagnostic(expr, ctx, arena, name, ctx.Out());
    ctx.RequestFinish();
    return MakeLogic4VecVal(arena, 1, 0);
  }
  Logic4Vec annex_d_result;
  if (TryEvalAnnexDFunction(expr, ctx, arena, name, annex_d_result)) {
    return annex_d_result;
  }
  Logic4Vec coverage_result;
  if (TryEvalCoverageSysCall(expr, ctx, arena, name, coverage_result)) {
    return coverage_result;
  }
  if (TryEvalAnnexDInteractiveTask(expr, ctx, arena, name, annex_d_result)) {
    return annex_d_result;
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
