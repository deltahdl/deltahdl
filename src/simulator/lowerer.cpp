#include "simulator/lowerer.h"

#include <algorithm>
#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "parser/ast.h"
#include "simulator/awaiters.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/stmt_exec.h"

namespace delta {

Lowerer::Lowerer(SimContext& ctx, Arena& arena, DiagEngine&)
    : ctx_(ctx), arena_(arena) {}

static SimCoroutine MakeInitialCoroutine(const Stmt* body, SimContext& ctx,
                                         Arena& arena) {
  co_await ExecStmt(body, ctx, arena);
}

static SimCoroutine MakeProgramInitialCoroutine(const Stmt* body,
                                                SimContext& ctx, Arena& arena) {
  co_await ExecStmt(body, ctx, arena);
  ctx.OnProgramInitialComplete(ctx.CurrentProcess());
}

static SimCoroutine MakeAlwaysCoroutine(const Stmt* body, SimContext& ctx,
                                        Arena& arena) {
  while (!ctx.StopRequested()) {
    auto result = co_await ExecStmt(body, ctx, arena);
    if (result != StmtResult::kDone) break;
  }
}

static SimCoroutine MakeAlwaysSensCoroutine(const Stmt* body,
                                            const std::vector<EventExpr>& sens,
                                            SimContext& ctx, Arena& arena) {
  while (!ctx.StopRequested()) {
    co_await EventAwaiter{ctx, sens, arena};

    ctx.FlushPendingViolations();
    auto result = co_await ExecStmt(body, ctx, arena);
    if (result != StmtResult::kDone) break;
  }
}

static SimCoroutine MakeAlwaysCombCoroutine(const Stmt* body, SimContext& ctx,
                                            Arena& arena) {
  auto read_strs = CollectReadSignals(body);
  std::vector<std::string_view> read_vars(read_strs.begin(), read_strs.end());
  while (!ctx.StopRequested()) {
    co_await ExecStmt(body, ctx, arena);
    if (read_vars.empty()) break;
    co_await AnyChangeAwaiter{ctx, read_vars};

    ctx.FlushPendingViolations();
  }
}

static Strength ParserStrToStrength(uint8_t s) {
  switch (s) {
    case 1:
      return Strength::kHighz;
    case 2:
      return Strength::kWeak;
    case 3:
      return Strength::kPull;
    case 4:
      return Strength::kStrong;
    case 5:
      return Strength::kSupply;
    default:
      return Strength::kStrong;
  }
}

static bool Logic4VecEqual(const Logic4Vec& a, const Logic4Vec& b) {
  if (a.nwords != b.nwords) return false;
  for (uint32_t i = 0; i < a.nwords; ++i) {
    if (a.words[i].aval != b.words[i].aval ||
        a.words[i].bval != b.words[i].bval)
      return false;
  }
  return true;
}

static bool IsAllHighZ(const Logic4Vec& v) {
  for (uint32_t i = 0; i < v.nwords; ++i) {
    if (v.words[i].aval != 0 || v.words[i].bval == 0) return false;
  }
  return v.nwords > 0;
}

static Logic4Vec ApplyHighzStrengthsToValue(const Logic4Vec& val,
                                            DriverStrength ds, Arena& arena) {
  bool s0_is_z = (ds.s0 == Strength::kHighz);
  bool s1_is_z = (ds.s1 == Strength::kHighz);
  if (!s0_is_z && !s1_is_z) return val;
  auto out = MakeLogic4Vec(arena, val.width);
  out.is_real = val.is_real;
  out.is_signed = val.is_signed;
  out.is_string = val.is_string;
  for (uint32_t w = 0; w < val.nwords; ++w) {
    uint64_t a = val.words[w].aval;
    uint64_t b = val.words[w].bval;
    uint64_t mask = ~uint64_t{0};
    uint32_t bits_done = w * 64;
    if (val.width > bits_done && val.width - bits_done < 64)
      mask = (uint64_t{1} << (val.width - bits_done)) - 1;
    uint64_t to_z = 0;
    if (s0_is_z) to_z |= (~a & ~b) & mask;
    if (s1_is_z) to_z |= (a & ~b) & mask;
    out.words[w].aval = a | to_z;
    out.words[w].bval = b | to_z;
  }
  return out;
}

struct ContAssignDelays {
  uint64_t rise = 0;
  uint64_t fall = 0;
  uint64_t decay = 0;
  bool has_fall = false;
  bool has_decay = false;
};

struct ContAssignDelayExprs {
  const Expr* rise = nullptr;
  const Expr* fall = nullptr;
  const Expr* decay = nullptr;
};

struct ContAssignParams {
  const Expr* lhs;
  const Expr* rhs;
  DriverStrength ds;
  ContAssignDelayExprs delays;
  uint32_t width = 0;

  bool nonresistive_switch = false;

  bool resistive_switch = false;
  const Expr* data_input = nullptr;
};

static uint64_t SelectScalarContAssignDelay(const Logic4Vec& old_val,
                                            const Logic4Vec& new_val,
                                            const ContAssignDelays& d) {
  bool new_has_x = HasUnknownBits(new_val);
  if (new_has_x) {
    uint64_t m = std::min(d.rise, d.fall);
    if (d.has_decay) m = std::min(m, d.decay);
    return m;
  }
  if (HasUnknownBits(old_val) || IsAllHighZ(old_val)) {
    // Old value is x or z, new value is a known 0 or 1. The destination
    // logic level selects the slot: 0 routes through the fall delay and 1
    // through the rise delay, matching the x/z-source rows of Table 28-9.
    return new_val.ToUint64() == 0 ? d.fall : d.rise;
  }
  uint64_t nv = new_val.ToUint64();
  uint64_t ov = old_val.ToUint64();
  if (nv > ov) return d.rise;
  if (nv < ov) return d.fall;
  return d.rise;
}

static uint64_t SelectContAssignDelay(const Logic4Vec& old_val,
                                      const Logic4Vec& new_val,
                                      const ContAssignDelays& d,
                                      uint32_t width) {
  if (!d.has_fall) return d.rise;

  bool new_is_z = IsAllHighZ(new_val);
  if (new_is_z) {
    if (d.has_decay) return d.decay;
    return std::min(d.rise, d.fall);
  }

  if (width <= 1) {
    return SelectScalarContAssignDelay(old_val, new_val, d);
  }

  if (!HasUnknownBits(new_val) && new_val.ToUint64() == 0 &&
      !HasUnknownBits(old_val) && !IsAllHighZ(old_val) &&
      old_val.ToUint64() != 0) {
    return d.fall;
  }
  return d.rise;
}

static ContAssignDelays BuildContAssignDelays(const ContAssignDelayExprs& exprs,
                                              SimContext& ctx, Arena& arena) {
  ContAssignDelays d;
  d.rise = EvalExpr(exprs.rise, ctx, arena).ToUint64();
  d.fall = exprs.fall ? EvalExpr(exprs.fall, ctx, arena).ToUint64() : 0;
  d.decay = exprs.decay ? EvalExpr(exprs.decay, ctx, arena).ToUint64() : 0;
  d.has_fall = exprs.fall != nullptr;
  d.has_decay = exprs.decay != nullptr;
  return d;
}

static DriverStrength ComputeEffectiveDriverStrength(
    const ContAssignParams& params, SimContext& ctx) {
  DriverStrength effective_ds = params.ds;
  if ((params.nonresistive_switch || params.resistive_switch) &&
      params.data_input && params.data_input->kind == ExprKind::kIdentifier) {
    auto* data_net = ctx.FindNet(params.data_input->text);
    if (data_net) {
      const NetStrength& ns = data_net->resolved_strength;
      auto reduce =
          params.resistive_switch ? &ReduceResistive : &ReduceNonresistive;
      effective_ds.s0 = reduce(ns.s0_hi);
      effective_ds.s1 = reduce(ns.s1_hi);
    }
  }
  return effective_ds;
}

static void ApplyContAssignResult(const ContAssignParams& params, Net* net,
                                  size_t driver_idx, bool first,
                                  const Logic4Vec& driven_val,
                                  DriverStrength effective_ds, SimContext& ctx,
                                  Arena& arena) {
  if (net) {
    if (first) {
      net->drivers.push_back(driven_val);
      net->driver_strengths.push_back(effective_ds);
    } else {
      net->drivers[driver_idx] = driven_val;
      net->driver_strengths[driver_idx] = effective_ds;
    }
    net->Resolve(arena);
  } else {
    auto* var = ctx.FindVariable(params.lhs->text);
    if (var && !var->is_forced) {
      var->value = ResizeToWidth(driven_val, var->value.width, arena);
      var->NotifyWatchers();
    }
  }
}

static SimCoroutine MakeContAssignCoroutine(ContAssignParams params,
                                            SimContext& ctx, Arena& arena) {
  if (!params.lhs || params.lhs->kind != ExprKind::kIdentifier) co_return;

  std::unordered_set<std::string> read_strs;
  CollectExprReads(params.rhs, read_strs);
  std::vector<std::string_view> read_vars(read_strs.begin(), read_strs.end());

  auto* net = ctx.FindNet(params.lhs->text);
  size_t driver_idx = net ? net->drivers.size() : 0;
  bool first = true;

  while (!ctx.StopRequested()) {
    auto val = EvalExpr(params.rhs, ctx, arena, params.width);

    if (params.delays.rise) {
      ContAssignDelays d = BuildContAssignDelays(params.delays, ctx, arena);

      Logic4Vec old_val = MakeLogic4VecVal(arena, 1, 0);
      auto* var = ctx.FindVariable(params.lhs->text);
      if (var)
        old_val = var->value;
      else if (net && net->resolved)
        old_val = net->resolved->value;

      uint64_t ticks = SelectContAssignDelay(old_val, val, d, params.width);
      if (ticks > 0 && !read_vars.empty()) {
        SimTime target = ctx.CurrentTime() + SimTime{ticks};
        while (true) {
          uint64_t remaining = (target.ticks > ctx.CurrentTime().ticks)
                                   ? (target.ticks - ctx.CurrentTime().ticks)
                                   : 0;
          if (remaining == 0) break;
          bool expired =
              co_await InertialDelayAwaiter{ctx, remaining, read_vars};
          if (expired) break;
          auto new_val = EvalExpr(params.rhs, ctx, arena, params.width);
          if (!Logic4VecEqual(new_val, val)) {
            // The operand changed again before the pending value could
            // propagate, so the previously scheduled event is dropped.
            val = new_val;
            if (Logic4VecEqual(new_val, old_val)) {
              // The re-evaluated right-hand side now matches the value already
              // present on the left-hand side, so no replacement event is
              // scheduled and the pending transition collapses immediately.
              break;
            }
            ticks = SelectContAssignDelay(old_val, val, d, params.width);
            target = ctx.CurrentTime() + SimTime{ticks};
          }
        }
      } else if (ticks > 0) {
        co_await DelayAwaiter{ctx, ticks};
      }
    }

    DriverStrength effective_ds = ComputeEffectiveDriverStrength(params, ctx);

    auto driven_val = ApplyHighzStrengthsToValue(val, effective_ds, arena);

    ApplyContAssignResult(params, net, driver_idx, first, driven_val,
                          effective_ds, ctx, arena);

    first = false;

    if (read_vars.empty()) break;
    co_await AnyChangeAwaiter{ctx, read_vars};
  }
}

static void ScheduleProcess(Process* proc, SimContext& ctx) {
  auto& sched = ctx.GetScheduler();
  auto* event = sched.GetEventPool().Acquire();

  event->kind = EventKind::kEvaluation;
  event->callback = [proc, &ctx]() {
    ctx.SetCurrentProcess(proc);
    proc->Resume();
  };
  sched.ScheduleEvent(SimTime{0}, proc->home_region, event);
}

void Lowerer::LowerProcesses(const std::vector<RtlirProcess>& procs,
                             bool from_program, uint32_t program_block_id) {
  for (const auto& proc : procs) {
    if (proc.kind != RtlirProcessKind::kInitial)
      LowerProcess(proc, from_program, program_block_id);
  }
  for (const auto& proc : procs) {
    if (proc.kind == RtlirProcessKind::kInitial)
      LowerProcess(proc, from_program, program_block_id);
  }
}

void Lowerer::LowerParams(const RtlirModule* mod) {
  for (const auto& p : mod->params) {
    if (p.is_unbounded) {
      ctx_.RegisterUnboundedParam(p.name);
      ctx_.CreateVariable(p.name, 32);
      continue;
    }
    if (!p.is_resolved) continue;
    auto* var = ctx_.CreateVariable(p.name, 32);
    var->value =
        MakeLogic4VecVal(arena_, 32, static_cast<uint64_t>(p.resolved_value));
  }
}

void Lowerer::LowerAliases(const RtlirModule* mod) {
  for (const auto& alias : mod->aliases) {
    if (alias.nets.size() < 2) continue;
    std::string_view primary;
    for (auto* net : alias.nets) {
      if (net->kind != ExprKind::kIdentifier) continue;
      if (primary.empty()) {
        primary = net->text;
      } else {
        ctx_.AliasVariable(net->text, primary);
      }
    }
  }
}

static void RegisterInstanceKeyBinding(const std::string& inst_prefix,
                                       std::string_view library,
                                       std::string_view name, SimContext& ctx) {
  std::string key = inst_prefix;
  if (!key.empty() && key.back() == '.') key.pop_back();
  ctx.RegisterInstanceType(key, name);
  // §33.7: record this instance's resolved library.cell so the %l/%L display
  // specifier can report its binding. The cell is the module's design-element
  // name; the library is the one it was compiled into.
  ctx.RegisterInstanceBinding(key, library, name);
}

static void RegisterModuleNets(const RtlirModule* mod, SimContext& ctx) {
  for (const auto& net : mod->nets) {
    ctx.CreateNet(net.name, net.net_type, net.width, net.charge_strength,
                  net.decay_ticks, net.is_user_nettype, net.resolve_func,
                  net.is_signed);
  }
}

static void RegisterModulePorts(const RtlirModule* mod, SimContext& ctx) {
  for (const auto& port : mod->ports) {
    if (!ctx.FindVariable(port.name)) {
      auto* v = ctx.CreateVariable(port.name, port.width);
      if (port.is_signed) v->is_signed = true;
    }
  }
}

static void RegisterModuleSubroutines(const RtlirModule* mod, SimContext& ctx) {
  for (auto* func : mod->function_decls) {
    ctx.RegisterFunction(func->name, func);
  }
  for (auto* let_decl : mod->let_decls) {
    ctx.RegisterLetDecl(let_decl->name, let_decl);
  }
}

static void RegisterModuleSequenceDecls(const RtlirModule* mod,
                                        SimContext& ctx) {
  for (auto* seq_decl : mod->sequence_decls) {
    ctx.RegisterSequenceDecl(seq_decl->name, seq_decl);

    std::string ep_name = std::string("__seq_") + std::string(seq_decl->name);
    if (!ctx.FindVariable(ep_name)) {
      auto* ep_var = ctx.CreateVariable(ep_name, 1);
      ep_var->is_event = true;
    }
  }
}

static void RegisterProcessClassType(SimContext& ctx, Arena& arena) {
  auto* proc_type = arena.Create<ClassTypeInfo>();
  proc_type->name = "process";
  proc_type->enum_members["FINISHED"] = 0;
  proc_type->enum_members["RUNNING"] = 1;
  proc_type->enum_members["WAITING"] = 2;
  proc_type->enum_members["SUSPENDED"] = 3;
  proc_type->enum_members["KILLED"] = 4;
  ctx.RegisterClassType("process", proc_type);
}

void Lowerer::LowerModule(const RtlirModule* mod) {
  RegisterInstanceKeyBinding(inst_prefix_, mod->library, mod->name, ctx_);
  LowerParams(mod);
  RegisterModuleNets(mod, ctx_);
  RegisterEnumTypes(mod);
  for (const auto& var : mod->variables) LowerVar(var);
  RegisterModulePorts(mod, ctx_);
  RegisterModuleSubroutines(mod, ctx_);
  RegisterModuleSequenceDecls(mod, ctx_);
  for (auto* cls : mod->class_decls) {
    LowerClassDecl(cls);
  }

  LowerImports(mod);
  RegisterProcessClassType(ctx_, arena_);
  LowerAliases(mod);
  uint32_t program_block_id = mod->is_program ? next_program_block_id_++ : 0;
  LowerProcesses(mod->processes, mod->is_program, program_block_id);
  for (const auto& ca : mod->assigns) {
    LowerContAssign(ca, mod->is_program);
  }

  LowerChildModules(mod);
}

static void RegisterSensitivity(const RtlirProcess& proc, Process* p,
                                SimContext& ctx) {
  auto signals = CollectReadSignals(proc.body);
  for (const auto& name : signals) {
    ctx.AddSensitivity(name, p);
  }
}

void Lowerer::LowerProcess(const RtlirProcess& proc, bool from_program,
                           uint32_t program_block_id) {
  auto* p = arena_.Create<Process>();
  p->id = next_id_++;

  p->home_region = from_program
                       ? Scheduler::HomeRegionForReactiveBlockingAssign()
                       : Region::kActive;
  p->is_reactive = from_program;
  p->inst_prefix = inst_prefix_;
  // §18.14.1: a static process is seeded with the next value from the
  // enclosing initialization RNG. Lowering happens before any thread runs, so
  // the active stream here is the context-wide generator, which embodies the
  // module's initialization RNG for this test harness.
  p->rng_seed = ctx_.DrawSeedForChild();

  switch (proc.kind) {
    case RtlirProcessKind::kInitial:
      p->kind = ProcessKind::kInitial;
      if (from_program) {
        ctx_.RegisterProgramInitial(program_block_id, p);
        p->coro =
            MakeProgramInitialCoroutine(proc.body, ctx_, arena_).Release();
      } else {
        p->coro = MakeInitialCoroutine(proc.body, ctx_, arena_).Release();
      }
      break;
    case RtlirProcessKind::kAlways:
      p->kind = ProcessKind::kAlways;
      if (!proc.sensitivity.empty() || proc.is_star_sensitivity) {
        p->coro =
            MakeAlwaysSensCoroutine(proc.body, proc.sensitivity, ctx_, arena_)
                .Release();
      } else {
        p->coro = MakeAlwaysCoroutine(proc.body, ctx_, arena_).Release();
      }
      break;
    case RtlirProcessKind::kAlwaysComb:
    case RtlirProcessKind::kAlwaysLatch:
      p->kind = ProcessKind::kAlwaysComb;
      p->coro = MakeAlwaysCombCoroutine(proc.body, ctx_, arena_).Release();
      RegisterSensitivity(proc, p, ctx_);
      break;
    case RtlirProcessKind::kAlwaysFF:
      p->kind = ProcessKind::kAlwaysFF;
      p->coro = MakeAlwaysCombCoroutine(proc.body, ctx_, arena_).Release();
      break;
    case RtlirProcessKind::kFinal:
      p->kind = ProcessKind::kFinal;
      p->coro = MakeInitialCoroutine(proc.body, ctx_, arena_).Release();
      ctx_.RegisterFinalProcess(p);
      return;
  }

  ScheduleProcess(p, ctx_);
}

void Lowerer::LowerContAssign(const RtlirContAssign& ca, bool from_program) {
  auto* p = arena_.Create<Process>();
  p->kind = ProcessKind::kContAssign;
  p->id = next_id_++;

  p->home_region = from_program
                       ? Scheduler::HomeRegionForReactiveBlockingAssign()
                       : Region::kActive;
  p->is_reactive = from_program;

  p->inst_prefix = inst_prefix_;
  ContAssignParams cap;
  cap.lhs = ca.lhs;
  cap.rhs = ca.rhs;
  cap.ds = {ParserStrToStrength(ca.drive_strength0),
            ParserStrToStrength(ca.drive_strength1)};
  cap.nonresistive_switch = ca.from_nonresistive_switch;
  cap.resistive_switch = ca.from_resistive_switch;
  cap.data_input = ca.data_input;
  cap.delays = {ca.delay, ca.delay_fall, ca.delay_decay};
  cap.width = ca.width;
  p->coro = MakeContAssignCoroutine(cap, ctx_, arena_).Release();

  ScheduleProcess(p, ctx_);
}

PackageDecl* Lowerer::FindPackage(std::string_view name) const {
  if (!design_) return nullptr;
  for (auto* pkg : design_->packages) {
    if (pkg->name == name) return pkg;
  }
  return nullptr;
}

void Lowerer::LowerPackageItem(ModuleItem* item) {
  if (item->kind == ModuleItemKind::kClassDecl && item->class_decl) {
    if (!ctx_.FindClassType(item->class_decl->name)) {
      LowerClassDecl(item->class_decl);
    }
  } else if (item->kind == ModuleItemKind::kFunctionDecl ||
             item->kind == ModuleItemKind::kTaskDecl) {
    if (!ctx_.FindFunction(item->name)) {
      ctx_.RegisterFunction(item->name, item);
    }
  }
}

static bool PackageItemHasName(const ModuleItem* item, std::string_view name) {
  if (item->name == name) return true;
  if (item->kind == ModuleItemKind::kClassDecl && item->class_decl &&
      item->class_decl->name == name)
    return true;
  return false;
}

static bool IsImportOrExportDecl(const ModuleItem* item) {
  return item->kind == ModuleItemKind::kImportDecl ||
         item->kind == ModuleItemKind::kExportDecl;
}

static ModuleItem* FindNamedPackageItem(PackageDecl* pkg,
                                        std::string_view name) {
  for (auto* item : pkg->items) {
    if (IsImportOrExportDecl(item)) continue;
    if (PackageItemHasName(item, name)) return item;
  }
  return nullptr;
}

// Collects the package names imported by `pkg`, which a wildcard ("*")
// export re-exports from. The caller resolves each name and recurses.
static std::vector<std::string_view> WildcardExportImportNames(
    const PackageDecl* pkg) {
  std::vector<std::string_view> names;
  for (auto* imp_item : pkg->items) {
    if (imp_item->kind != ModuleItemKind::kImportDecl) continue;
    names.push_back(imp_item->import_item.package_name);
  }
  return names;
}

void Lowerer::LowerImportedName(
    PackageDecl* pkg, std::string_view name,
    std::unordered_set<const PackageDecl*>& visited) {
  if (!visited.insert(pkg).second) return;
  if (auto* found = FindNamedPackageItem(pkg, name)) {
    LowerPackageItem(found);
    return;
  }

  for (auto* item : pkg->items) {
    if (item->kind != ModuleItemKind::kExportDecl) continue;
    const auto& ex = item->import_item;
    if (ex.package_name == "*") {
      for (std::string_view src_name : WildcardExportImportNames(pkg)) {
        auto* src = FindPackage(src_name);
        if (!src) continue;
        auto sub = visited;
        LowerImportedName(src, name, sub);
      }
    } else if (ex.is_wildcard || ex.item_name == name) {
      auto* src = FindPackage(ex.package_name);
      if (!src) continue;
      auto sub = visited;
      LowerImportedName(src, name, sub);
    }
  }
}

void Lowerer::LowerAllImported(
    PackageDecl* pkg, std::unordered_set<const PackageDecl*>& visited) {
  if (!visited.insert(pkg).second) return;
  for (auto* item : pkg->items) {
    if (IsImportOrExportDecl(item)) continue;
    LowerPackageItem(item);
  }

  for (auto* item : pkg->items) {
    if (item->kind != ModuleItemKind::kExportDecl) continue;
    const auto& ex = item->import_item;
    if (ex.package_name == "*") {
      for (std::string_view src_name : WildcardExportImportNames(pkg)) {
        auto* src = FindPackage(src_name);
        if (!src) continue;
        auto sub = visited;
        LowerAllImported(src, sub);
      }
    } else {
      auto* src = FindPackage(ex.package_name);
      if (!src) continue;
      if (ex.is_wildcard) {
        auto sub = visited;
        LowerAllImported(src, sub);
      } else {
        auto sub = visited;
        LowerImportedName(src, ex.item_name, sub);
      }
    }
  }
}

static void AliasPackageDataItem(const PackageDecl* pkg, const ModuleItem* item,
                                 SimContext& ctx) {
  bool is_param = item->kind == ModuleItemKind::kParamDecl;
  bool is_var = item->kind == ModuleItemKind::kVarDecl;
  if (!(is_param || is_var) || !item->init_expr) return;
  if (ctx.FindVariable(item->name)) return;
  std::string qname = std::string(pkg->name) + "." + std::string(item->name);
  ctx.AliasVariable(item->name, qname);
}

void Lowerer::LowerImports(const RtlirModule* mod) {
  auto apply_import = [&](const RtlirImport& imp) {
    auto* pkg = FindPackage(imp.package_name);
    if (!pkg) return;
    std::unordered_set<const PackageDecl*> visited;
    if (imp.is_wildcard) {
      LowerAllImported(pkg, visited);
      for (const auto* item : pkg->items) AliasPackageDataItem(pkg, item, ctx_);
    } else {
      LowerImportedName(pkg, imp.item_name, visited);
      for (const auto* item : pkg->items) {
        if (item->name == imp.item_name) AliasPackageDataItem(pkg, item, ctx_);
      }
    }
  };

  // §26.5: an explicit import of a name takes precedence over a wildcard import
  // of the same name. Because alias_data_item lets the first binding of a name
  // win, the explicitly imported names must be bound before any wildcard import
  // is applied, regardless of the order the import declarations appear in the
  // source. Module-local declarations are materialized before LowerImports
  // runs, so they already shadow both kinds of import.
  for (const auto& imp : mod->imports)
    if (!imp.is_wildcard) apply_import(imp);
  for (const auto& imp : mod->imports)
    if (imp.is_wildcard) apply_import(imp);
}

static bool IsConnectablePortBinding(const RtlirPortBinding& binding) {
  if (!binding.connection) return false;
  if (binding.width == 0) return false;
  return binding.direction == Direction::kInput ||
         binding.direction == Direction::kOutput ||
         binding.direction == Direction::kInout;
}

static Expr* MakeLocalPortId(std::string_view port_name, Arena& arena) {
  auto* name_str = arena.Create<std::string>(std::string(port_name));
  auto* local_id = arena.Create<Expr>();
  local_id->kind = ExprKind::kIdentifier;
  local_id->text = *name_str;
  return local_id;
}

void Lowerer::LowerPortBindings(const RtlirModuleInst& inst,
                                bool from_program) {
  for (const auto& binding : inst.port_bindings) {
    if (!IsConnectablePortBinding(binding)) continue;

    auto* local_id = MakeLocalPortId(binding.port_name, arena_);

    if (binding.direction == Direction::kInout) {
      if (binding.connection->kind != ExprKind::kIdentifier) continue;
      std::string local_qualified =
          inst_prefix_ + std::string(binding.port_name);
      ctx_.AliasVariable(local_qualified, binding.connection->text);
      continue;
    }

    if (binding.direction == Direction::kInput) {
      RtlirContAssign ca;
      ca.lhs = local_id;
      ca.rhs = binding.connection;
      ca.width = binding.width;
      LowerContAssign(ca, from_program);
      continue;
    }

    if (binding.connection->kind != ExprKind::kIdentifier) continue;
    RtlirContAssign ca;
    ca.lhs = binding.connection;
    ca.rhs = local_id;
    ca.width = binding.width;
    LowerContAssign(ca, from_program);
  }
}

static void CreateChildModuleVariables(const std::string& inst_prefix,
                                       const RtlirModule* resolved,
                                       SimContext& ctx, Arena& arena) {
  for (const auto& var : resolved->variables) {
    auto* name = arena.Create<std::string>(inst_prefix + std::string(var.name));
    uint32_t width = var.class_type_name.empty() ? var.width : 64;
    if (var.is_real && width < 64) width = 64;
    auto* v = ctx.CreateVariable(*name, width);
    if (!var.is_4state && !var.is_event && !var.is_string && !var.is_chandle)
      v->value = MakeLogic4VecVal(arena, width, 0);
    if (var.is_chandle) v->value = MakeLogic4VecVal(arena, width, 0);
    v->is_4state = var.is_4state;
    if (var.is_event) v->is_event = true;
    if (var.is_signed) v->is_signed = true;
  }
}

static void CreateChildModulePorts(const std::string& inst_prefix,
                                   const RtlirModule* resolved, SimContext& ctx,
                                   Arena& arena) {
  for (const auto& port : resolved->ports) {
    auto* name =
        arena.Create<std::string>(inst_prefix + std::string(port.name));
    if (!ctx.FindVariable(*name)) {
      auto* v = ctx.CreateVariable(*name, port.width);
      if (port.is_signed) v->is_signed = true;
    }
  }
}

void Lowerer::LowerChildModules(const RtlirModule* mod) {
  for (const auto& child : mod->children) {
    if (!child.resolved) continue;
    auto saved_prefix = inst_prefix_;
    inst_prefix_ = inst_prefix_ + std::string(child.inst_name) + ".";

    RegisterInstanceKeyBinding(inst_prefix_, child.resolved->library,
                               child.resolved->name, ctx_);
    CreateChildModuleVariables(inst_prefix_, child.resolved, ctx_, arena_);
    CreateChildModulePorts(inst_prefix_, child.resolved, ctx_, arena_);

    LowerPortBindings(child, child.resolved->is_program);

    uint32_t child_block_id =
        child.resolved->is_program ? next_program_block_id_++ : 0;
    LowerProcesses(child.resolved->processes, child.resolved->is_program,
                   child_block_id);
    for (const auto& ca : child.resolved->assigns) {
      LowerContAssign(ca, child.resolved->is_program);
    }

    LowerChildModules(child.resolved);

    inst_prefix_ = saved_prefix;
  }
}

static void RegisterDesignTypeWidths(const RtlirDesign* design,
                                     SimContext& ctx) {
  for (const auto& [name, width] : design->type_widths) {
    ctx.RegisterTypeWidth(name, width);
  }
}

static void InitPackageDataVariables(const RtlirDesign* design, SimContext& ctx,
                                     Arena& arena) {
  for (auto* pkg : design->packages) {
    for (auto* item : pkg->items) {
      bool is_param = item->kind == ModuleItemKind::kParamDecl;
      bool is_var = item->kind == ModuleItemKind::kVarDecl;
      if (!(is_param || is_var) || !item->init_expr) continue;
      auto* qname = arena.Create<std::string>(std::string(pkg->name) + "." +
                                              std::string(item->name));
      auto* var = ctx.CreateVariable(*qname, 32);
      var->value = EvalExpr(item->init_expr, ctx, arena);
    }
  }
}

static void RegisterFreeCuFunctions(const RtlirDesign* design,
                                    SimContext& ctx) {
  for (auto* item : design->cu_function_decls) {
    if (!item->method_class.empty()) continue;
    ctx.RegisterFunction(item->name, item);
  }
}

static void AttachCuMethodsToClasses(const RtlirDesign* design,
                                     SimContext& ctx) {
  for (auto* item : design->cu_function_decls) {
    if (item->method_class.empty()) continue;
    auto* cls = ctx.FindClassType(item->method_class);
    if (!cls) continue;
    std::string name(item->name);
    cls->methods[name] = item;
  }
}

void Lowerer::Lower(const RtlirDesign* design) {
  if (!design) return;
  // §20.10.1: a $fatal or $error elaboration severity task that survived
  // generate expansion marks the design as not startable. Refuse to lower
  // any part of it so the scheduler sees an empty event calendar.
  if (design->simulation_blocked) return;
  design_ = design;
  // Annex D.11: the interactive scope consulted by the optional $scope system
  // task starts at the first top-level module. A later $scope call retargets
  // it.
  if (!design->top_modules.empty()) {
    ctx_.SetInteractiveScope(design->top_modules.front()->name);
  }
  RegisterDesignTypeWidths(design, ctx_);
  InitPackageDataVariables(design, ctx_, arena_);

  for (auto* cls : design->cu_class_decls) {
    if (!ctx_.FindClassType(cls->name)) {
      LowerClassDecl(cls);
    }
  }

  RegisterFreeCuFunctions(design, ctx_);
  for (auto* mod : design->top_modules) {
    LowerModule(mod);
  }

  for (auto* let_decl : design->cu_let_decls) {
    ctx_.RegisterLetDecl(let_decl->name, let_decl);
  }

  AttachCuMethodsToClasses(design, ctx_);
}

}  // namespace delta
