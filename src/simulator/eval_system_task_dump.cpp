#include <unistd.h>

#include <algorithm>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <optional>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "parser/ast.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/vcd_writer.h"

namespace delta {

// The four monitor task names listed in Syntax 21-3. They differ only in the
// default radix used for unformatted expression arguments; that radix is
// applied by the shared display machinery, so all four monitor identically.
bool IsMonitorTask(std::string_view name) {
  return name == "$monitor" || name == "$monitorb" || name == "$monitoro" ||
         name == "$monitorh";
}

// Gathers the simple signal names referenced anywhere in a monitor argument.
// $time, $stime, and $realtime are system calls rather than identifiers, so
// they are never collected and their advance does not trigger the monitor.
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

// Queues the active monitor's display into the postponed region of the current
// time step, coalescing so that simultaneous changes produce a single line.
static void ScheduleMonitorDisplay(SimContext& ctx, Arena& arena) {
  if (ctx.MonitorDisplayPending()) return;
  ctx.SetMonitorDisplayPending(true);
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->callback = [&ctx, &arena]() {
    ctx.SetMonitorDisplayPending(false);
    const Expr* monitor = ctx.ActiveMonitor();
    if (monitor == nullptr || !ctx.MonitorEnabled()) return;
    // §33.7: a redisplay is produced long after the call that installed the
    // list, so the instance the list was written in is reinstated for the span
    // of the output; the binding the %l/%L specifier reports belongs to that
    // instance and not to whichever process the value change happened to run
    // under.
    ctx.SetDeferredBindingScope(std::string(ctx.MonitorBindingScope()));
    ExecDisplayWrite(monitor, ctx, arena);
    ctx.SetDeferredBindingScope(std::nullopt);
    std::cout << "\n";
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kPostponed,
                                   event);
}

// Installs a persistent watcher that redisplays the active monitor whenever the
// signal takes on a new value. The captured generation deactivates the watcher
// once a later $monitor has replaced the display list.
static void AddMonitorWatcher(Variable* var, SimContext& ctx, Arena& arena,
                              uint64_t generation) {
  var->AddWatcher([var, &ctx, &arena, generation]() -> bool {
    if (generation != ctx.MonitorGeneration()) return true;  // superseded
    const Logic4Vec* last = ctx.MonitorLastValue(var);
    if (last != nullptr && SameBits(*last, var->value)) return false;
    ctx.SetMonitorLastValue(var, CloneLogic4Vec(var->value, arena));
    if (ctx.MonitorEnabled()) ScheduleMonitorDisplay(ctx, arena);
    return false;
  });
}

Logic4Vec EvalMonitor(const Expr* expr, SimContext& ctx, Arena& arena) {
  // A fresh $monitor call becomes the one active display list and supersedes
  // any earlier one.
  ctx.SetActiveMonitor(expr);
  // §33.7: the list is redisplayed on every change of a watched value, each
  // time from outside the process that installed it, so the instance this call
  // was written in is recorded alongside the list for the %l/%L specifier to
  // report the binding of.
  std::string monitor_scope;
  if (Process* proc = ctx.CurrentProcess()) monitor_scope = proc->inst_prefix;
  ctx.SetMonitorBindingScope(std::move(monitor_scope));
  std::vector<std::string_view> names;
  for (auto* arg : expr->args) CollectMonitorSignals(arg, names);
  uint64_t generation = ctx.MonitorGeneration();
  for (auto name : names) {
    Variable* var = ctx.FindVariable(name);
    if (var == nullptr) continue;
    ctx.SetMonitorLastValue(var, CloneLogic4Vec(var->value, arena));
    AddMonitorWatcher(var, ctx, arena, generation);
  }
  // The initial values are displayed at the end of the current time step.
  if (ctx.MonitorEnabled()) ScheduleMonitorDisplay(ctx, arena);
  return MakeLogic4VecVal(arena, 1, 0);
}

Logic4Vec EvalMonitorFlag(SimContext& ctx, Arena& arena,
                          std::string_view name) {
  if (name == "$monitoroff") {
    ctx.SetMonitorEnabled(false);
  } else {  // $monitoron
    ctx.SetMonitorEnabled(true);
    // Turning the flag on produces a display immediately, regardless of
    // whether a watched value has changed.
    ScheduleMonitorDisplay(ctx, arena);
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

// §21.7.2.3: the $version section of the VCD header reproduces the $dumpfile
// task that created the file, and when the filename was specified by a
// variable or an expression the unevaluated literal -- not the resolved
// string -- is what shall appear there. This renders the argument back to its
// source spelling: literals and identifiers keep their token text, and the
// composite forms are rebuilt from their parts.
static std::string DumpfileArgSourceText(const Expr* arg);

// The comma-separated source text of an expression list, as written.
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
      // A function call naming the file keeps its call form -- the callee and
      // its (unevaluated) arguments -- not the string the call returns.
      return std::string(arg->callee) + "(" + DumpfileArgListText(arg->args) +
             ")";
    default:
      // Literals (a string literal keeps its quotes) and identifiers carry
      // their own source text.
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

// §21.7.3.1: the simulator performs the file-writing checks for the resolved
// $dumpports output name and reports problems rather than failing silently:
// the directory the name points into (the working directory for a bare name)
// must exist and be writable.
// `loc` is where the call was written. The name has already been resolved to
// a string by the time it is checked -- it may not even have been spelled out
// in the call -- so the call is the position the report names.
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

// §21.7.3.1: decide whether the trailing $dumpports argument denotes the
// filename. A string literal always does; an identifier does when it names a
// variable -- the filename may be a string-typed or integral variable holding
// a character string, whereas an identifier that names no variable is a
// module scope belonging to the scope_list.
static bool DumpportsLastArgIsFileName(const Expr* expr, SimContext& ctx) {
  if (expr->args.empty()) return false;
  const Expr* last = expr->args.back();
  if (last == nullptr) return false;
  if (last->kind == ExprKind::kStringLiteral) return true;
  return last->kind == ExprKind::kIdentifier &&
         ctx.FindVariable(last->text) != nullptr;
}

// Resolves the $dumpports output filename (§21.7.3.1). The filename is an
// expression given as a string literal, a string-typed variable, or an
// integral variable containing a character string; when no filename is
// supplied the output defaults to dumpports.vcd in the working directory.
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
    // A string or integral variable names the file through the character
    // string its evaluated value holds.
    return FormatValueAsString(EvalExpr(last, ctx, arena));
  }
  return "dumpports.vcd";
}

// §21.7.3.7: the extended VCD control tasks each act on a $dumpports dump and
// share the general rules for filename matching and no-argument default
// actions. $vcdclose is one of them: §21.7.3.6.1 gives it the extended VCD
// file, and §21.7.3.7 states its rules for every extended VCD system task.
static bool IsExtendedVcdControlTask(std::string_view name) {
  return name == "$dumpportsoff" || name == "$dumpportson" ||
         name == "$dumpportsall" || name == "$dumpportslimit" ||
         name == "$dumpportsflush" || name == "$vcdclose";
}

// §21.7.3.2: a control task's optional filename is its trailing argument and
// names which $dumpports output the task targets. Like the $dumpports filename
// itself, it may be a string literal, a string-typed variable, or an integral
// variable holding a character string; a variable is evaluated to recover the
// name it holds. Returns the resolved filename, or an empty string when the
// call carries no such argument ($dumpportslimit's sole argument is the
// filesize, so only its second argument can name a file).
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

// §21.7.1.2: reduce a $dumpvars scope argument to the name under which the
// selected object is registered. A plain identifier keeps its name and a string
// literal loses its quotes. A hierarchical reference such as top.mod2.net1
// parses as a chain of member accesses whose text is spread across the chain,
// so rebuild it into the dotted downward path (e.g. c1.val) that matches the
// key an instance's variable is registered under -- without this a
// member-access argument would carry no text of its own and be dropped.
// Flatten a hierarchical member access to its dotted path, outermost first.
static std::string FlattenHierPath(const Expr* arg) {
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

// §21.7.1.2: dump the variables named by a $dumpvars call. With no arguments
// every variable in the model is dumped. When arguments are present the first
// is the level count -- how many levels of the hierarchy below each named
// module instance to dump, with 0 meaning every level below -- and the
// remaining arguments name the scopes (whole module instances or individual
// variables) to dump. The level count never names a variable of its own and
// does not apply to scope arguments that name an individual variable.
static void ExecDumpvars(const Expr* expr, SimContext& ctx, Arena& arena,
                         VcdWriter* vcd) {
  if (!vcd) return;
  std::vector<std::string> scope_storage;
  for (size_t i = 1; i < expr->args.size(); ++i) {
    if (expr->args[i] == nullptr) continue;
    auto scope = DumpvarsScopePath(expr->args[i]);
    if (!scope.empty()) scope_storage.push_back(std::move(scope));
  }
  // §21.7.2.4: the checkpoint section follows the simulation_time command of
  // the time unit the task executed in, so the writer stamps that time first.
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

// §21.7.3.1: gather the unique module scopes named in a $dumpports scope_list.
// scope_end excludes a trailing filename argument. Only modules may be named:
// a string-literal entry is not a valid module_identifier and an entry naming
// a variable is rejected too. A hierarchical entry keeps its period-separated
// downward path. Duplicate scopes within this call and across earlier
// $dumpports calls are reported rather than dumped.
static std::vector<std::string> CollectDumpportsScopes(const Expr* expr,
                                                       size_t scope_end,
                                                       SimContext& ctx) {
  std::vector<std::string> scopes;
  for (size_t i = 0; i < scope_end; ++i) {
    if (!expr->args[i]) continue;
    // §21.7.3.1: scope_list entries name modules; a string literal is not a
    // valid module_identifier, so reject it rather than treating it as a
    // scope name.
    if (expr->args[i]->kind == ExprKind::kStringLiteral) {
      ctx.GetDiag().Error(
          expr->args[i]->range.start,
          "$dumpports scope_list entry must be a module, not a string "
          "literal",
          Subclause("21.7.3.1"));
      continue;
    }
    // A plain or hierarchical entry becomes the dotted path a module
    // instance's variables are registered under (e.g. c1 or c1.g1).
    std::string scope = DumpvarsScopePath(expr->args[i]);
    if (scope.empty()) continue;
    // §21.7.3.1: only modules are allowed in the scope_list; an entry that
    // resolves to a variable is rejected.
    if (ctx.FindVariable(scope) != nullptr) {
      ctx.GetDiag().Error(
          expr->args[i]->range.start,
          "$dumpports scope_list entry must be a module, not a variable",
          Subclause("21.7.3.1"));
      continue;
    }
    // §21.7.3.1: each scope named in a $dumpports scope_list shall be
    // unique; a repeated scope is reported rather than dumped twice.
    if (std::find(scopes.begin(), scopes.end(), scope) != scopes.end()) {
      ctx.GetDiag().Error(expr->args[i]->range.start,
                          "$dumpports scope_list entries must be unique",
                          Subclause("21.7.3.1"));
      continue;
    }
    // §21.7.3.1: scope names must also be unique across separate $dumpports
    // calls, not just within one call.
    if (!ctx.RegisterDumpportsScope(scope)) {
      ctx.GetDiag().Error(expr->args[i]->range.start,
                          "$dumpports scope already named by an earlier call",
                          Subclause("21.7.3.1"));
      continue;
    }
    scopes.push_back(std::move(scope));
  }
  return scopes;
}

// §21.7.3.1: name the (extended) VCD output and select the ports to dump. A
// trailing filename argument (string literal, or a string/integral variable
// holding the name) names the file, defaulting to dumpports.vcd when omitted.
// The leading arguments form the scope_list naming the modules whose ports
// are dumped; with no scope_list the scope is the calling module, so every
// port registered from the point of the call is treated as a primary I/O pin
// and dumped. The value change dumping itself starts at the end of the
// current simulation time unit, so the opening checkpoint is scheduled on the
// writer rather than emitted here. Dumping reuses the 4-state VCD machinery,
// which the extended VCD file inherits unless otherwise stated.
static void ExecDumpports(const Expr* expr, SimContext& ctx, Arena& arena) {
  // §21.7.3.1: $dumpports can be invoked multiple times, but every execution
  // shall be at the same simulation time.
  if (!ctx.RegisterDumpportsTime(ctx.CurrentTime().ticks)) {
    ctx.GetDiag().Error(
        expr->range.start,
        "all $dumpports tasks must execute at the same simulation time",
        Subclause("21.7.3.1"));
    return;
  }
  bool last_is_file = DumpportsLastArgIsFileName(expr, ctx);
  ctx.SetDumpFileName(ResolveDumpportsFileName(expr, ctx, arena, last_is_file));
  // §21.7.3.1: the simulator checks that the named file is writable and
  // reports an error when it is not.
  CheckDumpportsFileWritable(ctx.GetDumpFileName(), ctx, expr->range.start);
  // §21.7.3.1: a file name spelled out in the call may not be reused by a
  // later $dumpports call. A defaulted name is not "specified", so repeated
  // default calls are allowed.
  if (last_is_file && !ctx.RegisterDumpportsFile(ctx.GetDumpFileName())) {
    ctx.GetDiag().Error(
        expr->range.start,
        "$dumpports may not name the same output file more than once",
        Subclause("21.7.3.1"));
  }
  // §21.7.1: $dumpports is one of the VCD system tasks a source inserts to
  // create a dump file, so the file named above is opened here rather than
  // waiting for something outside the source to open one. §21.7 b) makes what
  // it opens the extended type -- variable changes in all states and strength
  // information -- and the type is stated at the open because §21.7.4.2's node
  // information goes out with the definitions, before this task returns.
  VcdWriter* vcd = ctx.OpenVcdDumpFromTask(VcdFileType::kExtended);
  if (!vcd) return;
  // $dumpports produces an extended VCD file, which closes with the
  // $vcdclose keyword command (§21.7.3.6.1). Marking the writer here as well
  // as at the open covers a dump this call found already open, whose node
  // information is on disk in whatever form opened it: §21.7.3.6.1 records the
  // final simulation time "at the time the extended VCD file is closed", which
  // is still writable then, while the definitions above it are not.
  vcd->SetExtended();
  size_t scope_end = expr->args.size() - (last_is_file ? 1 : 0);
  std::vector<std::string> scopes =
      CollectDumpportsScopes(expr, scope_end, ctx);
  vcd->SchedulePortDumpStart(std::move(scopes), ctx.CurrentTime().ticks);
}

// §21.7.3.7: an extended VCD control task that names a file no $dumpports call
// opened is ignored. The match is against the files explicitly named by
// $dumpports; with no filename argument the default action runs against every
// such file. Under this single-writer model, when no $dumpports call has named
// a file there is nothing to mismatch, so the lone dump is the implicit target
// and the task proceeds. Returns true when the task should be skipped.
static bool DumpportsControlTaskTargetsUnknownFile(const Expr* expr,
                                                   SimContext& ctx,
                                                   Arena& arena,
                                                   std::string_view name) {
  if (!IsExtendedVcdControlTask(name) || !ctx.HasDumpportsFiles()) return false;
  std::string file = DumpportsControlFileArg(expr, ctx, arena, name);
  return !file.empty() && !ctx.IsDumpportsFile(file);
}

// §21.7.1.5 / §21.7.3.4: bound the VCD file size in bytes. The single (leading)
// argument gives the maximum byte budget; the extended-VCD form reuses the same
// 4-state size-limit machinery the file inherits.
static void ExecDumpLimit(const Expr* expr, SimContext& ctx, Arena& arena,
                          VcdWriter* vcd) {
  if (vcd && !expr->args.empty()) {
    uint64_t limit = EvalExpr(expr->args[0], ctx, arena).ToUint64();
    vcd->SetSizeLimit(limit);
  }
}

// §21.7.1.x: the basic four-state VCD control tasks ($dumpall/$dumpoff/$dumpon/
// $dumpflush) act directly on the writer. Returns true when name named one of
// them (whether or not a writer is present) so the caller stops dispatching.
static bool ExecBasicVcdControl(std::string_view name, VcdWriter* vcd,
                                SimContext& ctx) {
  // §21.7.2.4: each checkpoint section sits after the simulation_time command
  // of its execution time, so the timed writer entry points are used.
  uint64_t now = ctx.CurrentTime().ticks;
  if (name == "$dumpall") {
    // Emit a checkpoint of every selected variable's current value (§21.7.1.4).
    if (vcd) vcd->DumpAll(now);
  } else if (name == "$dumpoff") {
    // Suspend dumping with an all-x checkpoint (§21.7.1.3).
    if (vcd) vcd->DumpOff(now);
  } else if (name == "$dumpon") {
    // Resume dumping with a checkpoint of current values (§21.7.1.3).
    if (vcd) vcd->DumpOn(now);
  } else if (name == "$dumpflush") {
    // §21.7.1.6: flush buffered output to the dump file, then continue dumping
    // as before so no value changes are lost.
    if (vcd) vcd->Flush();
  } else {
    return false;
  }
  return true;
}

// §21.7.3.x: the writer-acting extended-VCD ($dumpports) port control tasks.
// Each reuses the 4-state machinery the extended VCD file inherits and treats
// its optional trailing filename as selecting this single-file writer (already
// validated by DumpportsControlTaskTargetsUnknownFile). Returns true when name
// named one of them (whether or not a writer is present) so the caller stops
// dispatching.
static bool ExecDumpportsWriterAction(std::string_view name, SimContext& ctx,
                                      VcdWriter* vcd) {
  // §21.7.3.2: the suspend and resume checkpoints belong to the simulation
  // time the task executed at, so their sections sit after that time's marker.
  uint64_t now = ctx.CurrentTime().ticks;
  if (name == "$dumpportsoff") {
    // §21.7.3.2: suspend the extended VCD port dump. A checkpoint marking every
    // selected port as x is written and recording stops from this simulation
    // time forward. The optional filename argument denotes the $dumpports
    // output file; with this single-file writer it selects that one dump, and
    // with no argument every $dumpports file is suspended. The suspend
    // checkpoint reuses the 4-state machinery the extended VCD file inherits
    // (§21.7.1.3). If port dumping is already suspended for the file the task
    // is ignored, so no second checkpoint is written.
    if (vcd && vcd->IsEnabled()) vcd->DumpOff(now);
  } else if (name == "$dumpportson") {
    // §21.7.3.2: resume the extended VCD port dump, emitting a checkpoint of
    // every selected port's current value. The optional filename argument names
    // the $dumpports file to resume; with no argument every stopped $dumpports
    // file resumes. The resume checkpoint reuses the inherited 4-state
    // machinery (§21.7.1.3). If the ports are already being dumped the task is
    // ignored, so no checkpoint is written.
    if (vcd && !vcd->IsEnabled()) vcd->DumpOn(now);
  } else if (name == "$dumpportsall") {
    // §21.7.3.3: write an extended-VCD checkpoint recording the current value
    // of every selected port at this simulation time, regardless of whether the
    // values changed since the previous time step. The optional filename names
    // the $dumpports output to checkpoint; with this single-file writer it
    // selects that one dump, and with no filename the checkpoint covers every
    // file opened by $dumpports. The checkpoint reuses the 4-state machinery
    // the extended VCD file inherits (§21.7.1.4), including the placement of
    // its section after the #<time> marker of the executing simulation time.
    if (vcd) vcd->DumpAll(now);
  } else if (name == "$dumpportsflush") {
    // §21.7.3.5: push the buffered extended-VCD port values out to the dump
    // file, clearing the simulator's VCD buffer so a reader sees everything
    // dumped so far while the simulation keeps running. The optional filename
    // argument denotes the $dumpports output to flush; with this single-file
    // writer it selects that one dump, and with no filename the buffers for
    // every file opened by $dumpports are flushed. Either way the one writer is
    // flushed, so the filename is parsed but does not change which dump is
    // emptied. The flush reuses the buffer-flushing machinery the extended VCD
    // file inherits (§21.7.1.6): no VCD command is written and the dump state
    // is left untouched so dumping continues exactly as before.
    if (vcd) vcd->Flush();
  } else {
    return false;
  }
  return true;
}

// §21.7.3.x: the extended-VCD ($dumpports) port control tasks. The
// writer-acting tasks are handled by ExecDumpportsWriterAction; $dumpportslimit
// additionally needs the call expression to read its byte budget. Returns true
// when name named one of these tasks so the caller stops dispatching.
static bool ExecDumpportsControl(const Expr* expr, SimContext& ctx,
                                 Arena& arena, VcdWriter* vcd,
                                 std::string_view name) {
  if (name == "$dumpportslimit") {
    // §21.7.3.4: bound the extended VCD file size. The required leading
    // filesize argument gives the maximum number of bytes; once the dump
    // reaches it, recording stops and a comment noting the limit is inserted. A
    // trailing filename argument may denote which $dumpports output the limit
    // applies to; with no filename the limit covers every file opened by
    // $dumpports. With this single-file writer both cases bound the one dump,
    // so the optional filename is parsed but does not change which dump is
    // limited. The byte budget reuses the 4-state size-limit machinery the
    // extended VCD file inherits (§21.7.1.5).
    //
    // §21.7.3.4: the filesize argument is required. A call that carries no
    // leading argument names no byte budget to apply, so it is reported
    // rather than silently accepted.
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

// §21.7.3.6.1: terminate the extended VCD file, recording the final simulation
// time. The keyword command states the time "at the time the extended VCD file
// is closed", so the task closes the dump as well as stamping it: closing here
// is what stops the per-timestep recording, which would otherwise write value
// changes after the command that terminates the file. The time written is the
// simulation time the task executes at, which is that closing moment.
//
// §21.7.3.6 adds the keyword to the extended VCD format alone -- Table 21-10
// lists the 4-state keyword commands and $vcdclose is not among them -- so a
// dump opened by $dumpfile or $dumpvars is neither stamped nor closed, and goes
// on recording. That is the same outcome §21.7.3.7 gives a control task naming
// a file no $dumpports call opened.
static void ExecVcdClose(SimContext& ctx, VcdWriter* vcd) {
  if (vcd == nullptr || !vcd->IsExtended()) return;
  ctx.CloseVcdDump();
}

// The system tasks of §21.7 that write a value change dump. Every task named in
// §21.7.1 and §21.7.3.1 through §21.7.3.5 shares the $dump prefix; $vcdclose is
// the one that does not, being the keyword command §21.7.3.6 adds to the
// extended format rather than a member of the $dumpports family.
bool IsVcdSysCall(std::string_view name) {
  return name.starts_with("$dump") || name == "$vcdclose";
}

Logic4Vec EvalVcdSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                         std::string_view name) {
  auto* vcd = ctx.GetVcdWriter();
  if (DumpportsControlTaskTargetsUnknownFile(expr, ctx, arena, name)) {
    return MakeLogic4VecVal(arena, 1, 0);
  }
  if (name == "$dumpfile") {
    // §21.7.2.3: remember the filename argument exactly as written so the
    // $version section can reproduce the $dumpfile call unevaluated.
    ctx.SetDumpFileLiteral(expr->args.empty()
                               ? std::string{}
                               : DumpfileArgSourceText(expr->args[0]));
    ctx.SetDumpFileName(ResolveDumpFileName(expr, ctx, arena));
    // §21.7.1: Figure 21-1 has the source's own $dumpfile call produce the VCD
    // file, so the dump is opened here under the name just recorded. §21.7.1
    // is the 4-state file's subclause, so that is the type $dumpfile creates.
    ctx.OpenVcdDumpFromTask(VcdFileType::kFourState);
  } else if (name == "$dumpvars") {
    // §21.7.1.2: $dumpvars lists the variables to dump "into the file
    // specified by $dumpfile", which §21.7.1.1 defaults to "dump.vcd" when the
    // source named none. Either way the file exists from this call on, so a
    // source that reaches $dumpvars without a $dumpfile still gets a dump.
    ExecDumpvars(expr, ctx, arena,
                 ctx.OpenVcdDumpFromTask(VcdFileType::kFourState));
  } else if (name == "$dumplimit") {
    // §21.7.1.5: the single argument bounds the VCD file size in bytes. A
    // limit on a dump no task has opened bounds nothing, so this opens no
    // file of its own; §21.7.1 gives that job to the three tasks above.
    ExecDumpLimit(expr, ctx, arena, vcd);
  } else if (name == "$dumpports") {
    ExecDumpports(expr, ctx, arena);
  } else if (name == "$vcdclose") {
    ExecVcdClose(ctx, vcd);
  } else if (!ExecBasicVcdControl(name, vcd, ctx)) {
    ExecDumpportsControl(expr, ctx, arena, vcd, name);
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

}  // namespace delta
