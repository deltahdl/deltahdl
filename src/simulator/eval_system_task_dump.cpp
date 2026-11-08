#include <sys/unistd.h>
#include <unistd.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/deferred_caller.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_systask_internal.h"
#include "simulator/evaluation.h"
#include "simulator/file_monitor.h"
#include "simulator/monitor_member_watch.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/vcd_writer.h"

namespace delta {

bool IsMonitorTask(std::string_view name) {
  return name == "$monitor" || name == "$monitorb" || name == "$monitoro" ||
         name == "$monitorh";
}

static void CollectMonitorSignals(const Expr* e,
                                  std::vector<std::string_view>& out) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kIdentifier) {
    out.push_back(e->text);
    return;
  }
  CollectMonitorSignals(e->lhs, out);
  CollectMonitorSignals(e->rhs, out);
  CollectMonitorSignals(e->condition, out);
  CollectMonitorSignals(e->true_expr, out);
  CollectMonitorSignals(e->false_expr, out);
  CollectMonitorSignals(e->base, out);
  CollectMonitorSignals(e->index, out);
  CollectMonitorSignals(e->index_end, out);
  for (auto* a : e->args) CollectMonitorSignals(a, out);
  for (auto* el : e->elements) CollectMonitorSignals(el, out);
}

static Logic4Vec CloneLogic4Vec(const Logic4Vec& v, Arena& arena) {
  Logic4Vec copy = MakeLogic4Vec(arena, v.width);
  copy.is_signed = v.is_signed;
  uint32_t n = std::min(copy.nwords, v.nwords);
  for (uint32_t i = 0; i < n; ++i) copy.words[i] = v.words[i];
  return copy;
}

static bool SameBits(const Logic4Vec& a, const Logic4Vec& b) {
  if (a.nwords != b.nwords) return false;
  for (uint32_t i = 0; i < a.nwords; ++i) {
    if (a.words[i].aval != b.words[i].aval ||
        a.words[i].bval != b.words[i].bval)
      return false;
  }
  return true;
}

static void ScheduleMonitorDisplay(SimContext& ctx, Arena& arena) {
  if (ctx.MonitorDisplayPending()) return;
  ctx.SetMonitorDisplayPending(true);
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->callback = [&ctx, &arena]() {
    ctx.SetMonitorDisplayPending(false);
    const Expr* monitor = ctx.ActiveMonitor();
    if (monitor == nullptr || !ctx.MonitorEnabled()) return;
    Process* caller = ctx.MonitorCaller();
    CallerStandIn stand_in(caller, ctx);
    ctx.SetDeferredBindingScope(caller ? caller->inst_prefix : std::string());
    ExecDisplayWrite(monitor, ctx, arena);
    ctx.SetDeferredBindingScope(std::nullopt);
    ctx.Out() << "\n";
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kPostponed,
                                   event);
}

static void AddMonitorWatcher(Variable* var, SimContext& ctx, Arena& arena,
                              uint64_t generation) {
  var->AddWatcher([var, &ctx, &arena, generation]() -> bool {
    if (generation != ctx.MonitorGeneration()) return true;
    const Logic4Vec* last = ctx.MonitorLastValue(var);
    if (last != nullptr && SameBits(*last, var->value)) return false;
    ctx.SetMonitorLastValue(var, CloneLogic4Vec(var->value, arena));
    if (ctx.MonitorEnabled()) ScheduleMonitorDisplay(ctx, arena);
    return false;
  });
}

Logic4Vec EvalMonitor(const Expr* expr, SimContext& ctx, Arena& arena) {
  ctx.SetActiveMonitor(expr);
  ctx.SetMonitorCaller(SnapshotCallingProcess(ctx));
  std::vector<std::string_view> names;
  for (auto* arg : expr->args) CollectMonitorSignals(arg, names);
  uint64_t generation = ctx.MonitorGeneration();
  for (auto name : names) {
    Variable* var = ctx.FindVariable(name);
    if (var == nullptr) continue;
    ctx.SetMonitorLastValue(var, CloneLogic4Vec(var->value, arena));
    AddMonitorWatcher(var, ctx, arena, generation);
  }
  for (auto* arg : expr->args) {
    WatchClassMembersRead(arg, ctx, [&ctx, &arena, generation]() {
      if (generation != ctx.MonitorGeneration()) return true;
      if (ctx.MonitorEnabled()) ScheduleMonitorDisplay(ctx, arena);
      return false;
    });
  }
  if (ctx.MonitorEnabled()) ScheduleMonitorDisplay(ctx, arena);
  return MakeLogic4VecVal(arena, 1, 0);
}

static void ScheduleFileMonitorWrite(FileMonitor* monitor, SimContext& ctx,
                                     Arena& arena) {
  if (monitor->write_pending || monitor->cancelled) return;
  monitor->write_pending = true;
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->callback = [monitor, &ctx, &arena]() {
    monitor->write_pending = false;
    if (!monitor->cancelled) {
      CallerStandIn stand_in(monitor->caller.get(), ctx);
      ctx.SetDeferredBindingScope(monitor->scope);
      WriteFileOutputTask(monitor->call, monitor->descriptor,
                          monitor->task_name, ctx, arena);
      ctx.SetDeferredBindingScope(std::nullopt);
    }
    if (monitor->one_shot) {
      auto& all = ctx.FileMonitors();
      std::erase_if(all, [monitor](const std::unique_ptr<FileMonitor>& m) {
        return m.get() == monitor;
      });
    }
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kPostponed,
                                   event);
}

static void AddFileMonitorWatcher(Variable* var, FileMonitor* monitor,
                                  SimContext& ctx, Arena& arena) {
  var->AddWatcher([var, monitor, &ctx, &arena]() -> bool {
    if (monitor->cancelled) return true;
    auto last = monitor->last_values.find(var);
    if (last != monitor->last_values.end() &&
        SameBits(last->second, var->value))
      return false;
    monitor->last_values[var] = CloneLogic4Vec(var->value, arena);
    ScheduleFileMonitorWrite(monitor, ctx, arena);
    return false;
  });
}

static FileMonitor* AddFileMonitor(const Expr* expr, uint32_t descriptor,
                                   std::string_view name, SimContext& ctx) {
  auto owned = std::make_unique<FileMonitor>();
  FileMonitor* monitor = owned.get();
  monitor->call = expr;
  monitor->task_name = std::string(name);
  monitor->descriptor = descriptor;
  monitor->caller = SnapshotCallingProcess(ctx);
  if (monitor->caller != nullptr) monitor->scope = monitor->caller->inst_prefix;
  ctx.FileMonitors().push_back(std::move(owned));
  return monitor;
}

Logic4Vec EvalFstrobe(const Expr* expr, uint32_t descriptor,
                      std::string_view name, SimContext& ctx, Arena& arena) {
  FileMonitor* strobe = AddFileMonitor(expr, descriptor, name, ctx);
  strobe->one_shot = true;
  ScheduleFileMonitorWrite(strobe, ctx, arena);
  return MakeLogic4VecVal(arena, 1, 0);
}

Logic4Vec EvalFmonitor(const Expr* expr, uint32_t descriptor,
                       std::string_view name, SimContext& ctx, Arena& arena) {
  FileMonitor* monitor = AddFileMonitor(expr, descriptor, name, ctx);
  std::vector<std::string_view> names;
  for (size_t i = 1; i < expr->args.size(); ++i)
    CollectMonitorSignals(expr->args[i], names);
  for (auto var_name : names) {
    Variable* var = ctx.FindVariable(var_name);
    if (var == nullptr || monitor->last_values.count(var) != 0) continue;
    monitor->last_values[var] = CloneLogic4Vec(var->value, arena);
    AddFileMonitorWatcher(var, monitor, ctx, arena);
  }
  for (size_t i = 1; i < expr->args.size(); ++i) {
    WatchClassMembersRead(expr->args[i], ctx, [monitor, &ctx, &arena]() {
      if (monitor->cancelled) return true;
      ScheduleFileMonitorWrite(monitor, ctx, arena);
      return false;
    });
  }
  ScheduleFileMonitorWrite(monitor, ctx, arena);
  return MakeLogic4VecVal(arena, 1, 0);
}

Logic4Vec EvalMonitorFlag(SimContext& ctx, Arena& arena,
                          std::string_view name) {
  if (name == "$monitoroff") {
    ctx.SetMonitorEnabled(false);
  } else {
    ctx.SetMonitorEnabled(true);
    ScheduleMonitorDisplay(ctx, arena);
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

static std::string DumpfileArgSourceText(const Expr* arg);

static std::string DumpfileArgListText(const std::vector<Expr*>& list) {
  std::string text;
  for (size_t i = 0; i < list.size(); ++i) {
    if (i > 0) text += ",";
    text += DumpfileArgSourceText(list[i]);
  }
  return text;
}

static std::string DumpfileArgSourceText(const Expr* arg) {
  if (arg == nullptr) return {};
  switch (arg->kind) {
    case ExprKind::kMemberAccess:
      return DumpfileArgSourceText(arg->lhs) +
             (arg->is_scope_resolution ? "::" : ".") +
             DumpfileArgSourceText(arg->rhs);
    case ExprKind::kSelect: {
      std::string text = DumpfileArgSourceText(arg->base) + "[" +
                         DumpfileArgSourceText(arg->index);
      if (arg->index_end != nullptr) {
        text += ":" + DumpfileArgSourceText(arg->index_end);
      }
      return text + "]";
    }
    case ExprKind::kConcatenation:
      return "{" + DumpfileArgListText(arg->elements) + "}";
    case ExprKind::kCall:
      return std::string(arg->callee) + "(" + DumpfileArgListText(arg->args) +
             ")";
    default:
      return std::string(arg->text);
  }
}

static std::string ResolveDumpFileName(const Expr* expr, SimContext& ctx,
                                       Arena& arena) {
  if (expr->args.empty()) return "dump.vcd";
  const Expr* arg = expr->args[0];
  if (arg->kind == ExprKind::kStringLiteral) {
    auto text = arg->text;
    if (text.size() >= 2 && text.front() == '"') {
      return std::string(text.substr(1, text.size() - 2));
    }
    return std::string(text);
  }
  return FormatValueAsString(EvalExpr(arg, ctx, arena));
}

static void CheckDumpportsFileWritable(const std::string& name, SimContext& ctx,
                                       SourceLoc loc) {
  std::string dir = ".";
  auto slash = name.rfind('/');
  if (slash == 0) {
    dir = "/";
  } else if (slash != std::string::npos) {
    dir = name.substr(0, slash);
  }
  if (access(dir.c_str(), W_OK) != 0) {
    ctx.GetDiag().Error(loc,
                        "$dumpports cannot write dump file at path: " + name,
                        Subclause("21.7.3.1"));
  }
}

static bool DumpportsLastArgIsFileName(const Expr* expr, SimContext& ctx) {
  if (expr->args.empty()) return false;
  const Expr* last = expr->args.back();
  if (last == nullptr) return false;
  if (last->kind == ExprKind::kStringLiteral) return true;
  return last->kind == ExprKind::kIdentifier &&
         ctx.FindVariable(last->text) != nullptr;
}

static std::string ResolveDumpportsFileName(const Expr* expr, SimContext& ctx,
                                            Arena& arena, bool last_is_file) {
  if (last_is_file) {
    const Expr* last = expr->args.back();
    if (last->kind == ExprKind::kStringLiteral) {
      auto text = last->text;
      if (text.size() >= 2 && text.front() == '"') {
        return std::string(text.substr(1, text.size() - 2));
      }
      return std::string(text);
    }
    return FormatValueAsString(EvalExpr(last, ctx, arena));
  }
  return "dumpports.vcd";
}

static bool IsExtendedVcdControlTask(std::string_view name) {
  return name == "$dumpportsoff" || name == "$dumpportson" ||
         name == "$dumpportsall" || name == "$dumpportslimit" ||
         name == "$dumpportsflush" || name == "$vcdclose";
}

static std::string DumpportsControlFileArg(const Expr* expr, SimContext& ctx,
                                           Arena& arena,
                                           std::string_view name) {
  if (expr->args.empty()) return {};
  if (name == "$dumpportslimit" && expr->args.size() < 2) return {};
  const Expr* last = expr->args.back();
  if (last == nullptr) return {};
  if (last->kind == ExprKind::kStringLiteral) {
    auto text = last->text;
    if (text.size() >= 2 && text.front() == '"') {
      return std::string(text.substr(1, text.size() - 2));
    }
    return std::string(text);
  }
  if (last->kind == ExprKind::kIdentifier &&
      ctx.FindVariable(last->text) != nullptr) {
    return FormatValueAsString(EvalExpr(last, ctx, arena));
  }
  return {};
}

std::string FlattenHierPath(const Expr* arg) {
  std::vector<std::string_view> parts;
  const Expr* e = arg;
  while (e != nullptr && e->kind == ExprKind::kMemberAccess) {
    if (e->rhs != nullptr) parts.push_back(e->rhs->text);
    e = e->lhs;
  }
  if (e != nullptr) parts.push_back(e->text);
  std::string path;
  for (auto it = parts.rbegin(); it != parts.rend(); ++it) {
    if (!path.empty()) path.push_back('.');
    path.append(*it);
  }
  return path;
}

static std::string DumpvarsScopePath(const Expr* arg) {
  if (arg->kind == ExprKind::kMemberAccess) return FlattenHierPath(arg);
  std::string_view text = arg->text;
  if (arg->kind == ExprKind::kStringLiteral && text.size() >= 2 &&
      text.front() == '"') {
    text = text.substr(1, text.size() - 2);
  }
  return std::string(text);
}

static void ExecDumpvars(const Expr* expr, SimContext& ctx, Arena& arena,
                         VcdWriter* vcd) {
  if (!ctx.Vcd().RegisterDumpvarsTime(ctx.CurrentTime().ticks)) {
    ctx.GetDiag().Error(
        expr->range.start,
        "all $dumpvars tasks must execute at the same simulation time",
        Subclause("21.7.1.2"));
    return;
  }
  if (!vcd) return;
  std::vector<std::string> scope_storage;
  for (size_t i = 1; i < expr->args.size(); ++i) {
    if (expr->args[i] == nullptr) continue;
    auto scope = DumpvarsScopePath(expr->args[i]);
    if (!scope.empty()) scope_storage.push_back(std::move(scope));
  }
  uint64_t now = ctx.CurrentTime().ticks;
  if (scope_storage.empty()) {
    vcd->DumpAllValues(now);
    return;
  }
  uint64_t level = 0;
  if (!expr->args.empty() && expr->args[0] != nullptr) {
    level = EvalExpr(expr->args[0], ctx, arena).ToUint64();
  }
  std::vector<std::string_view> scopes(scope_storage.begin(),
                                       scope_storage.end());
  vcd->DumpScopeSelectedValues(scopes, level, now);
}

static std::vector<std::string> CollectDumpportsScopes(const Expr* expr,
                                                       size_t scope_end,
                                                       SimContext& ctx) {
  std::vector<std::string> scopes;
  for (size_t i = 0; i < scope_end; ++i) {
    if (!expr->args[i]) continue;
    if (expr->args[i]->kind == ExprKind::kStringLiteral) {
      ctx.GetDiag().Error(
          expr->args[i]->range.start,
          "$dumpports scope_list entry must be a module, not a string "
          "literal",
          Subclause("21.7.3.1"));
      continue;
    }
    std::string scope = DumpvarsScopePath(expr->args[i]);
    if (scope.empty()) continue;
    if (ctx.FindVariable(scope) != nullptr) {
      ctx.GetDiag().Error(
          expr->args[i]->range.start,
          "$dumpports scope_list entry must be a module, not a variable",
          Subclause("21.7.3.1"));
      continue;
    }
    if (std::find(scopes.begin(), scopes.end(), scope) != scopes.end()) {
      ctx.GetDiag().Error(expr->args[i]->range.start,
                          "$dumpports scope_list entries must be unique",
                          Subclause("21.7.3.1"));
      continue;
    }
    if (!ctx.Vcd().RegisterDumpportsScope(scope)) {
      ctx.GetDiag().Error(expr->args[i]->range.start,
                          "$dumpports scope already named by an earlier call",
                          Subclause("21.7.3.1"));
      continue;
    }
    scopes.push_back(std::move(scope));
  }
  return scopes;
}

static void ExecDumpports(const Expr* expr, SimContext& ctx, Arena& arena) {
  if (!ctx.Vcd().RegisterDumpportsTime(ctx.CurrentTime().ticks)) {
    ctx.GetDiag().Error(
        expr->range.start,
        "all $dumpports tasks must execute at the same simulation time",
        Subclause("21.7.3.1"));
    return;
  }
  ctx.Vcd().AddDumpportsCommand("$dumpports(" +
                                DumpfileArgListText(expr->args) + ")");
  bool last_is_file = DumpportsLastArgIsFileName(expr, ctx);
  ctx.Vcd().SetDumpportsFileName(
      ResolveDumpportsFileName(expr, ctx, arena, last_is_file));
  CheckDumpportsFileWritable(ctx.Vcd().GetDumpportsFileName(), ctx,
                             expr->range.start);
  if (last_is_file &&
      !ctx.Vcd().RegisterDumpportsFile(ctx.Vcd().GetDumpportsFileName())) {
    ctx.GetDiag().Error(
        expr->range.start,
        "$dumpports may not name the same output file more than once",
        Subclause("21.7.3.1"));
  }
  VcdWriter* vcd = ctx.OpenVcdDumpFromTask(VcdFileType::kExtended);
  if (!vcd) return;
  vcd->SetExtended();
  size_t scope_end = expr->args.size() - (last_is_file ? 1 : 0);
  std::vector<std::string> scopes =
      CollectDumpportsScopes(expr, scope_end, ctx);
  vcd->SchedulePortDumpStart(std::move(scopes), ctx.CurrentTime().ticks);
}

static bool DumpportsControlTaskTargetsUnknownFile(const Expr* expr,
                                                   SimContext& ctx,
                                                   Arena& arena,
                                                   std::string_view name) {
  if (!IsExtendedVcdControlTask(name) || !ctx.Vcd().HasDumpportsFiles())
    return false;
  std::string file = DumpportsControlFileArg(expr, ctx, arena, name);
  return !file.empty() && !ctx.Vcd().IsDumpportsFile(file);
}

static void ExecDumpLimit(const Expr* expr, SimContext& ctx, Arena& arena,
                          VcdWriter* vcd) {
  if (vcd && !expr->args.empty()) {
    uint64_t limit = EvalExpr(expr->args[0], ctx, arena).ToUint64();
    vcd->SetSizeLimit(limit);
  }
}

static bool ExecBasicVcdControl(std::string_view name, VcdWriter* vcd,
                                SimContext& ctx) {
  uint64_t now = ctx.CurrentTime().ticks;
  if (name == "$dumpall") {
    if (vcd) vcd->DumpAll(now);
  } else if (name == "$dumpoff") {
    if (vcd) vcd->DumpOff(now);
  } else if (name == "$dumpon") {
    if (vcd) vcd->DumpOn(now);
  } else if (name == "$dumpflush") {
    if (vcd) vcd->Flush();
  } else {
    return false;
  }
  return true;
}

static bool ExecDumpportsWriterAction(std::string_view name, SimContext& ctx,
                                      VcdWriter* vcd) {
  uint64_t now = ctx.CurrentTime().ticks;
  if (name == "$dumpportsoff") {
    if (vcd && vcd->IsEnabled()) vcd->DumpOff(now);
  } else if (name == "$dumpportson") {
    if (vcd && !vcd->IsEnabled()) vcd->DumpOn(now);
  } else if (name == "$dumpportsall") {
    if (vcd) vcd->DumpAll(now);
  } else if (name == "$dumpportsflush") {
    if (vcd) vcd->Flush();
  } else {
    return false;
  }
  return true;
}

static bool ExecDumpportsControl(const Expr* expr, SimContext& ctx,
                                 Arena& arena, VcdWriter* vcd,
                                 std::string_view name) {
  if (name == "$dumpportslimit") {
    if (expr->args.empty() || expr->args[0] == nullptr) {
      ctx.GetDiag().Error(expr->range.start,
                          "$dumpportslimit requires a filesize argument",
                          Subclause("21.7.3.4"));
      return true;
    }
    ExecDumpLimit(expr, ctx, arena, vcd);
    return true;
  }
  return ExecDumpportsWriterAction(name, ctx, vcd);
}

static void ExecVcdClose(SimContext& ctx) {
  VcdWriter* vcd = ctx.Vcd().GetDumpportsWriter();
  if (vcd == nullptr || !vcd->IsExtended()) return;
  ctx.CloseDumpportsDump();
}

bool IsVcdSysCall(std::string_view name) {
  return name == "$dumpfile" || name == "$dumpvars" || name == "$dumpoff" ||
         name == "$dumpon" || name == "$dumpall" || name == "$dumplimit" ||
         name == "$dumpflush" || name == "$dumpports" ||
         name == "$dumpportsoff" || name == "$dumpportson" ||
         name == "$dumpportsall" || name == "$dumpportslimit" ||
         name == "$dumpportsflush" || name == "$vcdclose";
}

Logic4Vec EvalVcdSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                         std::string_view name) {
  if (DumpportsControlTaskTargetsUnknownFile(expr, ctx, arena, name)) {
    return MakeLogic4VecVal(arena, 1, 0);
  }
  if (name == "$dumpfile") {
    ctx.Vcd().SetDumpFileLiteral(expr->args.empty()
                                     ? std::string{}
                                     : DumpfileArgSourceText(expr->args[0]));
    ctx.Vcd().SetDumpFileName(ResolveDumpFileName(expr, ctx, arena));
    ctx.OpenVcdDumpFromTask(VcdFileType::kFourState);
  } else if (name == "$dumpvars") {
    ExecDumpvars(expr, ctx, arena,
                 ctx.OpenVcdDumpFromTask(VcdFileType::kFourState));
  } else if (name == "$dumplimit") {
    ExecDumpLimit(expr, ctx, arena, ctx.Vcd().GetVcdWriter());
  } else if (name == "$dumpports") {
    ExecDumpports(expr, ctx, arena);
  } else if (name == "$vcdclose") {
    ExecVcdClose(ctx);
  } else if (!ExecBasicVcdControl(name, ctx.Vcd().GetVcdWriter(), ctx)) {
    ExecDumpportsControl(expr, ctx, arena, ctx.Vcd().GetDumpportsWriter(),
                         name);
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

}  // namespace delta
