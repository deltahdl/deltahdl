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

  if (!HasUnknownBits(new_val) && new_val.ToUint64() == 0 &&
      !HasUnknownBits(old_val) && !IsAllHighZ(old_val) &&
      old_val.ToUint64() != 0) {
    return d.fall;
  }
  return d.rise;
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
      ContAssignDelays d;
      d.rise = EvalExpr(params.delays.rise, ctx, arena).ToUint64();
      d.fall = params.delays.fall
                   ? EvalExpr(params.delays.fall, ctx, arena).ToUint64()
                   : 0;
      d.decay = params.delays.decay
                    ? EvalExpr(params.delays.decay, ctx, arena).ToUint64()
                    : 0;
      d.has_fall = params.delays.fall != nullptr;
      d.has_decay = params.delays.decay != nullptr;

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

    auto driven_val = ApplyHighzStrengthsToValue(val, effective_ds, arena);

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

void Lowerer::LowerModule(const RtlirModule* mod) {
  {
    std::string key = inst_prefix_;
    if (!key.empty() && key.back() == '.') key.pop_back();
    ctx_.RegisterInstanceType(key, mod->name);
    // §33.7: record this instance's resolved library.cell so the %l/%L display
    // specifier can report its binding. The cell is the module's design-element
    // name; the library is the one it was compiled into.
    ctx_.RegisterInstanceBinding(key, mod->library, mod->name);
  }
  LowerParams(mod);
  for (const auto& net : mod->nets) {
    ctx_.CreateNet(net.name, net.net_type, net.width, net.charge_strength,
                   net.decay_ticks, net.is_user_nettype, net.resolve_func,
                   net.is_signed);
  }
  RegisterEnumTypes(mod);
  for (const auto& var : mod->variables) LowerVar(var);
  for (const auto& port : mod->ports) {
    if (!ctx_.FindVariable(port.name)) {
      auto* v = ctx_.CreateVariable(port.name, port.width);
      if (port.is_signed) v->is_signed = true;
    }
  }
  for (auto* func : mod->function_decls) {
    ctx_.RegisterFunction(func->name, func);
  }
  for (auto* let_decl : mod->let_decls) {
    ctx_.RegisterLetDecl(let_decl->name, let_decl);
  }
  for (auto* seq_decl : mod->sequence_decls) {
    ctx_.RegisterSequenceDecl(seq_decl->name, seq_decl);

    std::string ep_name = std::string("__seq_") + std::string(seq_decl->name);
    if (!ctx_.FindVariable(ep_name)) {
      auto* ep_var = ctx_.CreateVariable(ep_name, 1);
      ep_var->is_event = true;
    }
  }
  for (auto* cls : mod->class_decls) {
    LowerClassDecl(cls);
  }

  LowerImports(mod);
  {
    auto* proc_type = arena_.Create<ClassTypeInfo>();
    proc_type->name = "process";
    proc_type->enum_members["FINISHED"] = 0;
    proc_type->enum_members["RUNNING"] = 1;
    proc_type->enum_members["WAITING"] = 2;
    proc_type->enum_members["SUSPENDED"] = 3;
    proc_type->enum_members["KILLED"] = 4;
    ctx_.RegisterClassType("process", proc_type);
  }
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

void Lowerer::LowerImportedName(
    PackageDecl* pkg, std::string_view name,
    std::unordered_set<const PackageDecl*>& visited) {
  if (!visited.insert(pkg).second) return;
  for (auto* item : pkg->items) {
    if (item->kind == ModuleItemKind::kImportDecl ||
        item->kind == ModuleItemKind::kExportDecl)
      continue;
    if (PackageItemHasName(item, name)) {
      LowerPackageItem(item);
      return;
    }
  }

  for (auto* item : pkg->items) {
    if (item->kind != ModuleItemKind::kExportDecl) continue;
    const auto& ex = item->import_item;
    if (ex.package_name == "*") {
      for (auto* imp_item : pkg->items) {
        if (imp_item->kind != ModuleItemKind::kImportDecl) continue;
        auto* src = FindPackage(imp_item->import_item.package_name);
        if (!src) continue;
        auto sub = visited;
        LowerImportedName(src, name, sub);
      }
    } else if (ex.is_wildcard) {
      auto* src = FindPackage(ex.package_name);
      if (!src) continue;
      auto sub = visited;
      LowerImportedName(src, name, sub);
    } else if (ex.item_name == name) {
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
    if (item->kind == ModuleItemKind::kImportDecl ||
        item->kind == ModuleItemKind::kExportDecl)
      continue;
    LowerPackageItem(item);
  }

  for (auto* item : pkg->items) {
    if (item->kind != ModuleItemKind::kExportDecl) continue;
    const auto& ex = item->import_item;
    if (ex.package_name == "*") {
      for (auto* imp_item : pkg->items) {
        if (imp_item->kind != ModuleItemKind::kImportDecl) continue;
        auto* src = FindPackage(imp_item->import_item.package_name);
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

void Lowerer::LowerImports(const RtlirModule* mod) {
  auto alias_data_item = [&](const PackageDecl* pkg, const ModuleItem* item) {
    bool is_param = item->kind == ModuleItemKind::kParamDecl;
    bool is_var = item->kind == ModuleItemKind::kVarDecl;
    if (!(is_param || is_var) || !item->init_expr) return;
    if (ctx_.FindVariable(item->name)) return;
    std::string qname = std::string(pkg->name) + "." + std::string(item->name);
    ctx_.AliasVariable(item->name, qname);
  };

  auto apply_import = [&](const RtlirImport& imp) {
    auto* pkg = FindPackage(imp.package_name);
    if (!pkg) return;
    std::unordered_set<const PackageDecl*> visited;
    if (imp.is_wildcard) {
      LowerAllImported(pkg, visited);
      for (const auto* item : pkg->items) alias_data_item(pkg, item);
    } else {
      LowerImportedName(pkg, imp.item_name, visited);
      for (const auto* item : pkg->items) {
        if (item->name == imp.item_name) alias_data_item(pkg, item);
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

void Lowerer::LowerPortBindings(const RtlirModuleInst& inst,
                                bool from_program) {
  for (const auto& binding : inst.port_bindings) {
    if (!binding.connection) continue;
    if (binding.width == 0) continue;
    if (binding.direction != Direction::kInput &&
        binding.direction != Direction::kOutput &&
        binding.direction != Direction::kInout) {
      continue;
    }

    auto* name_str = arena_.Create<std::string>(std::string(binding.port_name));
    auto* local_id = arena_.Create<Expr>();
    local_id->kind = ExprKind::kIdentifier;
    local_id->text = *name_str;

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

void Lowerer::LowerChildModules(const RtlirModule* mod) {
  for (const auto& child : mod->children) {
    if (!child.resolved) continue;
    auto saved_prefix = inst_prefix_;
    inst_prefix_ = inst_prefix_ + std::string(child.inst_name) + ".";

    {
      std::string key = inst_prefix_;
      if (!key.empty() && key.back() == '.') key.pop_back();
      ctx_.RegisterInstanceType(key, child.resolved->name);
      // §33.7: record the child instance's resolved library.cell binding for
      // the %l/%L display specifier.
      ctx_.RegisterInstanceBinding(key, child.resolved->library,
                                   child.resolved->name);
    }

    for (const auto& var : child.resolved->variables) {
      auto* name =
          arena_.Create<std::string>(inst_prefix_ + std::string(var.name));
      uint32_t width = var.class_type_name.empty() ? var.width : 64;
      if (var.is_real && width < 64) width = 64;
      auto* v = ctx_.CreateVariable(*name, width);
      if (!var.is_4state && !var.is_event && !var.is_string && !var.is_chandle)
        v->value = MakeLogic4VecVal(arena_, width, 0);
      if (var.is_chandle) v->value = MakeLogic4VecVal(arena_, width, 0);
      v->is_4state = var.is_4state;
      if (var.is_event) v->is_event = true;
      if (var.is_signed) v->is_signed = true;
    }

    for (const auto& port : child.resolved->ports) {
      auto* name =
          arena_.Create<std::string>(inst_prefix_ + std::string(port.name));
      if (!ctx_.FindVariable(*name)) {
        auto* v = ctx_.CreateVariable(*name, port.width);
        if (port.is_signed) v->is_signed = true;
      }
    }

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
  for (const auto& [name, width] : design->type_widths) {
    ctx_.RegisterTypeWidth(name, width);
  }

  for (auto* pkg : design->packages) {
    for (auto* item : pkg->items) {
      bool is_param = item->kind == ModuleItemKind::kParamDecl;
      bool is_var = item->kind == ModuleItemKind::kVarDecl;
      if (!(is_param || is_var) || !item->init_expr) continue;
      auto* qname = arena_.Create<std::string>(std::string(pkg->name) + "." +
                                               std::string(item->name));
      auto* var = ctx_.CreateVariable(*qname, 32);
      var->value = EvalExpr(item->init_expr, ctx_, arena_);
    }
  }

  for (auto* cls : design->cu_class_decls) {
    if (!ctx_.FindClassType(cls->name)) {
      LowerClassDecl(cls);
    }
  }

  for (auto* item : design->cu_function_decls) {
    if (!item->method_class.empty()) continue;
    ctx_.RegisterFunction(item->name, item);
  }
  for (auto* mod : design->top_modules) {
    LowerModule(mod);
  }

  for (auto* let_decl : design->cu_let_decls) {
    ctx_.RegisterLetDecl(let_decl->name, let_decl);
  }

  for (auto* item : design->cu_function_decls) {
    if (item->method_class.empty()) continue;
    auto* cls = ctx_.FindClassType(item->method_class);
    if (!cls) continue;
    std::string name(item->name);
    cls->methods[name] = item;
  }
}

}  // namespace delta
