#include "simulator/lowerer.h"

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "elaborator/design_scopes.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/global_clocking_sampled_value.h"
#include "elaborator/rtlir.h"
#include "elaborator/sdf_annotate_calls.h"
#include "elaborator/sensitivity.h"
#include "elaborator/time_literal_scale.h"
#include "elaborator/type_eval.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/assertion_read_names.h"
#include "simulator/awaiters.h"
#include "simulator/awaiters_event_control.h"
#include "simulator/class_object.h"
#include "simulator/code_coverage.h"
#include "simulator/coverage_control.h"
#include "simulator/disable_scope.h"
#include "simulator/dpi_export.h"
#include "simulator/dpi_formal_type.h"
#include "simulator/dpi_runtime.h"
#include "simulator/evaluation.h"
#include "simulator/expr_walk.h"
#include "simulator/lowerer_always_comb.h"
#include "simulator/lowerer_child.h"
#include "simulator/lowerer_register.h"
#include "simulator/module_path_delay.h"
#include "simulator/net.h"
#include "simulator/procedural_assertion.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/specify.h"
#include "simulator/specify_sdf.h"
#include "simulator/statement_assign.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_result.h"
#include "simulator/timing_check_delayed_signals.h"
#include "simulator/timing_check_driver.h"
#include "simulator/unit_scope_items.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_design_attach.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_systf_build.h"

namespace delta {

Lowerer::Lowerer(SimContext& ctx, Arena& arena, DiagEngine&)
    : ctx_(ctx), arena_(arena) {}

static SimCoroutine MakeInitialCoroutine(const Stmt* body, SimContext& ctx,
                                         Arena& arena) {
  Process* self = ctx.CurrentProcess();
  co_await ExecStmt(body, ctx, arena);
  if (self != nullptr) self->Finish();
  GetGlobalVpiContext().NoteThreadEnded(self);
}

static SimCoroutine MakeProgramInitialCoroutine(const Stmt* body,
                                                SimContext& ctx, Arena& arena) {
  Process* self = ctx.CurrentProcess();
  co_await ExecStmt(body, ctx, arena);
  ctx.OnProgramInitialComplete(ctx.CurrentProcess());
  if (self != nullptr) self->Finish();
  GetGlobalVpiContext().NoteThreadEnded(self);
}

static SimCoroutine MakeAlwaysCoroutine(const Stmt* body, SimContext& ctx,
                                        Arena& arena) {
  while (!ctx.StopRequested()) {
    auto result = co_await ExecStmt(body, ctx, arena);
    if (result != StmtResult::kDone) break;
  }
}

static bool IsPastDirectedFunction(std::string_view name) {
  return name == "$past" || name == "$rose" || name == "$fell" ||
         name == "$stable" || name == "$changed";
}

static std::vector<const Expr*> CollectPastDirectedSites(const Stmt* body) {
  std::vector<const Expr*> sites;
  ForEachStmtReadExpr(body, [&sites](const Expr* e) {
    ForEachSubExpr(e, [&sites](const Expr* sub) {
      if (sub->kind == ExprKind::kSystemCall &&
          IsPastDirectedFunction(sub->callee)) {
        sites.push_back(sub);
      }
    });
  });
  return sites;
}

static SimCoroutine MakeAlwaysSensCoroutine(const Stmt* body,
                                            const std::vector<EventExpr>& sens,
                                            bool reads_sampled, SimContext& ctx,
                                            Arena& arena) {
  std::vector<const Expr*> past_sites = CollectPastDirectedSites(body);
  while (!ctx.StopRequested()) {
    co_await EventAwaiter{ctx, sens, arena};
    for (const Expr* site : past_sites) EvalExpr(site, ctx, arena);

    ctx.FlushPendingViolations();
    ctx.FlushPendingDeferredReports();
    ctx.AssertionSamples().SetProcedureReadsSampled(reads_sampled);
    auto result = co_await ExecStmt(body, ctx, arena);
    ctx.AssertionSamples().SetProcedureReadsSampled(false);
    if (result != StmtResult::kDone) break;
  }
}

static SimCoroutine MakeAlwaysCombCoroutine(const Stmt* body,
                                            const std::vector<EventExpr>& sens,
                                            SimContext& ctx, Arena& arena) {
  std::vector<std::string_view> read_vars =
      AlwaysCombWatchedNames(body, sens, ctx);
  while (!ctx.StopRequested()) {
    co_await ExecStmt(body, ctx, arena);
    if (read_vars.empty()) break;
    co_await AnyChangeAwaiter{ctx, read_vars};

    ctx.FlushPendingViolations();
    ctx.FlushPendingDeferredReports();
  }
}

void ScheduleProcess(Process* proc, SimContext& ctx) {
  auto& sched = ctx.GetScheduler();
  auto* event = sched.GetEventPool().Acquire();

  event->kind = EventKind::kEvaluation;
  event->callback = [proc, &ctx]() {
    ctx.SetCurrentProcess(proc);
    proc->Resume();
  };
  if (proc->kind == ProcessKind::kAlwaysComb) {
    auto start = std::move(event->callback);
    event->callback = [proc, &ctx, start]() {
      auto* later = ctx.GetScheduler().GetEventPool().Acquire();
      later->kind = EventKind::kEvaluation;
      later->callback = start;
      ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), proc->home_region,
                                       later);
    };
  }
  sched.ScheduleEvent(SimTime{0}, proc->home_region, event);
}

void Lowerer::LowerProcesses(const std::vector<RtlirProcess>& procs,
                             bool from_program, uint32_t program_block_id) {
  for (const auto& proc : procs) {
    if (proc.kind != RtlirProcessKind::kInitial &&
        !KeepProceduralCheckerAssertion(proc))
      LowerProcess(proc, from_program, program_block_id);
  }
  for (const auto& proc : procs) {
    if (proc.kind == RtlirProcessKind::kInitial)
      LowerProcess(proc, from_program, program_block_id);
  }
}

std::string CoverageScopeOfInstanceKey(const std::string& key,
                                       const SimContext& ctx) {
  const std::string_view kTop = ctx.FirstTopModule();
  const std::string_view kHead = std::string_view(key).substr(0, key.find('.'));
  if (kTop.empty() || ctx.IsParallelTop(kHead)) return key;
  return key.empty() ? std::string(kTop) : std::string(kTop) + "." + key;
}

void RegisterInstanceKeyBinding(const std::string& inst_prefix,
                                const RtlirModule* mod, SimContext& ctx) {
  std::string_view library = mod->library;
  std::string_view name = mod->name;
  std::string key = inst_prefix;
  if (!key.empty() && key.back() == '.') key.pop_back();
  ctx.RegisterInstanceType(key, name);
  ctx.GetCoverageControlState().SetModuleDefinition(
      CoverageScopeOfInstanceKey(key, ctx), std::string(name));
  ctx.RegisterInstanceBinding(key, library, name);
  if (!mod->config.empty()) ctx.RegisterInstanceConfig(key, mod->config);
}

void Lowerer::RecordSpecifyScope(const RtlirModule* mod) {
  if (mod->specify_blocks.empty() && mod->gate_insts.empty() &&
      mod->specparam_names.empty()) {
    return;
  }
  specify_scopes_.push_back(SpecifyScope{inst_prefix_, mod});
}

void Lowerer::LowerModule(const RtlirModule* mod) {
  EnterInstanceUnit(design_, mod, inst_prefix_, ctx_, arena_);
  instance_prefixes_.try_emplace(mod, inst_prefix_);
  RegisterInstanceKeyBinding(inst_prefix_, mod, ctx_);
  RegisterTypeRefCompares(inst_prefix_, mod, ctx_);
  LowerParams(mod);
  RecordSpecifyScope(mod);
  RegisterModuleNets(mod, ctx_, arena_);
  RegisterEnumTypes(mod);
  RegisterParamEnumTypes(mod);
  LowerImports(mod);
  for (auto* cls : mod->class_decls) {
    RegisterClassDecl(cls, mod->function_decls);
  }
  RegisterChildInstanceKeys(mod);
  for (const auto& var : mod->variables) LowerVar(var.name, var);
  RegisterModulePorts(mod, ctx_, arena_);
  RegisterModuleSubroutines(mod, ctx_);
  RegisterModuleLets(mod, inst_prefix_, ctx_);
  for (auto* cls : mod->class_decls) InitClassStaticProperties(cls);
  RegisterInstanceSubroutines(mod, std::string(mod->name) + ".", ctx_, arena_);
  RegisterGenBlockSubroutines(mod, inst_prefix_, inst_prefix_, ctx_, arena_);
  RegisterGenBlockSubroutines(mod, std::string(mod->name) + ".", inst_prefix_,
                              ctx_, arena_);
  RecordSubroutineAssertionSampleScopes(mod);
  RecordStaticLocalSubroutines(mod);
  DeclareModuleNamedScopes(*mod, inst_prefix_, ctx_);
  RegisterModuleDpiImports(mod, ctx_);
  RegisterModuleDpiExports(mod, inst_prefix_, ctx_);
  RegisterModuleSequenceDecls(mod, ctx_);
  LowerSequenceMonitors(mod);
  LowerFreeVariableSolver(mod);

  RegisterProcessClassType(ctx_, arena_);
  LowerAliases(mod);
  LowerModuleProcesses(mod);

  LowerClockingBlocks(mod);
  RegisterGenBlockMembers(mod);

  LowerChildModules(mod);
}

void Lowerer::LowerModuleProcesses(const RtlirModule* mod) {
  uint32_t program_block_id = mod->is_program ? next_program_block_id_++ : 0;
  bool reactive = mod->is_program || mod->is_checker;
  lowering_checker_ = mod->is_checker;
  LowerProcesses(mod->processes, reactive, program_block_id);
  lowering_checker_ = false;
  for (const auto& ca : mod->assigns) {
    LowerContAssign(ca, reactive);
  }
  for (const auto& sw : mod->bidir_switches) {
    LowerBidirSwitch(sw, mod->is_program);
  }
  for (const auto& udp_inst : mod->udp_insts) {
    LowerUdpInst(udp_inst, mod->is_program);
  }
}

static bool IsSampledValueFunction(std::string_view name) {
  return name == "$sampled" || name == "$past" || name == "$rose" ||
         name == "$fell" || name == "$stable" || name == "$changed" ||
         IsGlobalClockingSampledFunction(name);
}

static void CollectSampledFunctionArgs(const Expr* e,
                                       std::unordered_set<std::string>& out) {
  ForEachSubExpr(e, [&out](const Expr* sub) {
    if (sub->kind == ExprKind::kSystemCall &&
        IsSampledValueFunction(sub->callee) && !sub->args.empty()) {
      CollectSampledOperandNames(sub->args[0], out);
    }
  });
}

static void CollectSampledFunctionArgsInStmt(
    const Stmt* stmt, std::unordered_set<std::string>& out) {
  if (stmt == nullptr) return;
  ForEachStmtReadExpr(
      stmt, [&out](const Expr* e) { CollectSampledFunctionArgs(e, out); });
}

static void CollectAssertionReadNames(const Stmt* stmt, SimContext& ctx,
                                      Arena& arena,
                                      std::unordered_set<std::string>& names) {
  if (stmt->assert_expr != nullptr) {
    CollectSampledOperandNames(stmt->assert_expr, names);
  }
  if (stmt->assert_sequence != nullptr) {
    CollectSequenceReadNames(stmt->assert_sequence, ctx, arena, names);
  }
  if (stmt->assert_property != nullptr) {
    CollectPropertyTreeReadNames(stmt->assert_property, ctx, arena, names);
  }
}

static void CollectProceduralAssertionReadNames(
    const Stmt* s, SimContext& ctx, Arena& arena,
    std::unordered_set<std::string>& names) {
  if (s == nullptr) return;
  if (s->is_procedural_concurrent && s->is_concurrent_clocked) {
    CollectAssertionReadNames(s, ctx, arena, names);
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CollectProceduralAssertionReadNames(sub, ctx, arena, names);
  });
}

void Lowerer::RecordAssertionSampleScope(const RtlirProcess& proc) {
  if (proc.body == nullptr) return;
  RecordAssertionSampleScope(proc.body);
  if (lowering_checker_ && proc.kind == RtlirProcessKind::kAlwaysFF) {
    AssertionSampleScope scope;
    scope.inst_prefix = inst_prefix_;
    std::unordered_set<std::string> names;
    ForEachStmtReadExpr(proc.body, [&names](const Expr* e) {
      CollectSampledOperandNames(e, names);
    });
    scope.names.assign(names.begin(), names.end());
    assertion_sample_scopes_.push_back(std::move(scope));
  }
}

void Lowerer::RecordAssertionSampleScope(const Stmt* body) {
  std::unordered_set<std::string> names;
  CollectAssertionReadNames(body, ctx_, arena_, names);
  CollectProceduralAssertionReadNames(body, ctx_, arena_, names);
  CollectSampledFunctionArgsInStmt(body, names);
  if (names.empty()) return;
  AssertionSampleScope scope;
  scope.inst_prefix = inst_prefix_;
  scope.names.assign(names.begin(), names.end());
  assertion_sample_scopes_.push_back(std::move(scope));
}

void Lowerer::RecordSubroutineAssertionSampleScopes(const RtlirModule* mod) {
  for (const ModuleItem* func : mod->function_decls) {
    for (const Stmt* s : func->func_body_stmts) {
      RecordAssertionSampleScope(s);
      LowerSampledClockMonitors(s);
    }
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
  p->origin = proc.body;
  p->is_concurrent_clocked = proc.is_concurrent_clocked;
  p->gclk_future_event = proc.gclk_future_event;
  RecordAssertionSampleScope(proc);
  LowerSampledClockMonitors(proc.body);
  p->rng_seed = ctx_.DrawSeedForChild();
  p->gen_prefixes.assign(proc.gen_block_prefixes.begin(),
                         proc.gen_block_prefixes.end());
  p->gen_block_name = GenBlockName(proc.gen_block_path);
  InstallGenBlockConsts(proc.gen_block_consts, p);
  RecordStaticLocalProcess(p, proc.body);

  if (proc.body != nullptr && proc.body->kind == StmtKind::kBlock &&
      !proc.body->label.empty()) {
    ctx_.RegisterOutermostScope(proc.body->label, p);
  }

  switch (proc.kind) {
    case RtlirProcessKind::kInitial:
      p->kind = ProcessKind::kInitial;
      if (program_block_id != 0) {
        ctx_.RegisterProgramInitial(program_block_id, p);
        p->coro =
            MakeProgramInitialCoroutine(proc.body, ctx_, arena_).Release();
      } else {
        p->coro = MakeInitialCoroutine(proc.body, ctx_, arena_).Release();
      }
      break;
    case RtlirProcessKind::kAlways:
      p->kind = ProcessKind::kAlways;
      if (proc.is_star_sensitivity) {
        p->coro =
            MakeAlwaysSensCoroutine(
                proc.body, ImplicitListEvents(proc.sensitivity, ctx_, arena_),
                false, ctx_, arena_)
                .Release();
      } else if (!proc.sensitivity.empty()) {
        p->coro = MakeAlwaysSensCoroutine(proc.body, proc.sensitivity, false,
                                          ctx_, arena_)
                      .Release();
      } else {
        p->coro = MakeAlwaysCoroutine(proc.body, ctx_, arena_).Release();
      }
      break;
    case RtlirProcessKind::kAlwaysComb:
    case RtlirProcessKind::kAlwaysLatch:
      p->kind = ProcessKind::kAlwaysComb;
      p->coro =
          MakeAlwaysCombCoroutine(proc.body, proc.sensitivity, ctx_, arena_)
              .Release();
      break;
    case RtlirProcessKind::kAlwaysFF:
      p->kind = ProcessKind::kAlwaysFF;
      p->coro = MakeAlwaysSensCoroutine(proc.body, ClockOf(proc),
                                        lowering_checker_, ctx_, arena_)
                    .Release();
      break;
    case RtlirProcessKind::kFinal:
      p->kind = ProcessKind::kFinal;
      p->coro = MakeInitialCoroutine(proc.body, ctx_, arena_).Release();
      ctx_.RegisterFinalProcess(p);
      return;
  }

  StartProceduralAssertionMonitors(p, proc.body, ctx_, arena_);
  RecordCheckerInstantiations(proc, p);
  ScheduleProcess(p, ctx_);
}

static int FinestPrecisionOrder(const RtlirModule* mod) {
  int order = EffectiveTimeOrder(mod->timescale.precision,
                                 mod->timescale.prec_magnitude);
  for (const auto& child : mod->children) {
    if (child.resolved != nullptr) {
      order = std::min(order, FinestPrecisionOrder(child.resolved));
    }
  }
  return order;
}

static TimeScale ScaleOfOrder(int order) {
  int base = order >= 0 ? (order / 3) * 3 : -(((-order) + 2) / 3) * 3;
  int magnitude = order - base == 2 ? 100 : (order - base == 1 ? 10 : 1);
  auto unit = static_cast<TimeUnit>(base);
  return TimeScale{unit, magnitude, unit, magnitude};
}

static void RegisterScopeTimescales(const RtlirModule* mod, SimContext& ctx,
                                    const std::string& from_top,
                                    const std::string& below_top) {
  ctx.SetScopeTimeScale(mod->name, mod->timescale);
  ctx.SetScopeTimeScale(from_top, mod->timescale);
  if (!below_top.empty()) ctx.SetScopeTimeScale(below_top, mod->timescale);
  for (const auto& child : mod->children) {
    if (!child.resolved) continue;
    std::string inst(child.inst_name);
    ctx.SetScopeTimeScale(inst, child.resolved->timescale);
    std::string child_from_top = from_top;
    child_from_top += ".";
    child_from_top += inst;
    std::string child_below_top = below_top;
    if (!child_below_top.empty()) child_below_top += ".";
    child_below_top += inst;
    RegisterScopeTimescales(child.resolved, ctx, child_from_top,
                            child_below_top);
  }
}

static void RegisterFreeCuFunctions(const RtlirDesign* design, SimContext& ctx,
                                    Arena& arena) {
  ForEachUnitScope(
      design, arena, [&](const CompilationUnit& unit, std::string_view scope) {
        for (auto* item : unit.cu_items) {
          if (!IsFreeUnitSubroutine(item)) continue;
          ctx.RegisterFunction(item->name, item);
          ctx.RegisterFunction(
              *arena.Create<std::string>(std::string(scope) +
                                         "::" + std::string(item->name)),
              item);
          ctx.RegisterSubroutinePackage(item, scope);
          ctx.RegisterStaticFrameOwner(item, scope);
        }
      });
}

static void BindInterconnectTopology(const RtlirDesign* design,
                                     SpecifyManager& mgr) {
  if (design->compilation_unit == nullptr || design->top_decls.empty()) return;
  if (design->top_decls.front() == nullptr) return;
  mgr.BindDesignInterconnect(CollectInterconnectTopology(
      *design->compilation_unit, *design->top_decls.front()));
}

void Lowerer::RegisterDesignTiming() {
  SpecifyManager& mgr = ctx_.AcquireSpecifyManager();
  BindInterconnectTopology(design_, mgr);
  for (const auto& scope : specify_scopes_) {
    ctx_.SetLoweringInstancePrefix(scope.inst_prefix);
    RegisterSpecifyBlocks(scope.module->specify_blocks, scope.inst_prefix, ctx_,
                          arena_, mgr);
    std::vector<std::string_view> module_outputs;
    for (const RtlirPort& port : scope.module->ports) {
      if (port.direction == Direction::kOutput ||
          port.direction == Direction::kInout) {
        module_outputs.push_back(port.name);
      }
    }
    RegisterModuleGates({scope.module->gate_insts, module_outputs},
                        scope.inst_prefix, ctx_, arena_, mgr);
    RegisterModuleSpecparams(scope.module->specparam_names, scope.inst_prefix,
                             ctx_, arena_, mgr);
    for (const RtlirVariable& var : scope.module->variables) {
      mgr.RecordSpecparamInitializer(scope.inst_prefix, var.name,
                                     var.init_expr);
    }
  }
  ctx_.SetLoweringInstancePrefix("");
  const auto kUnitTicks = static_cast<int64_t>(DelayToTicks(
      1, *ctx_.FindScopeTimeScale("$root"), ctx_.GlobalPrecision()));
  mgr.ResolveNegativeTimingCheckDelays(kUnitTicks, ctx_.GetDiag());
  WatchModulePathSources(mgr, ctx_);
  WatchTimingChecks(mgr, ctx_);
  DriveTimingCheckDelayedSignals(mgr, ctx_, arena_);
}

static void RegisterDesignScopes(const RtlirDesign* design, SimContext& ctx) {
  if (!design->top_modules.empty()) {
    ctx.SetInteractiveScope(design->top_modules.front()->name);
  }
  for (const std::string& name : CompleteHierarchicalScopeNames(design)) {
    ctx.RegisterHierarchicalScope(name);
  }
  for (ScopeDeclaredVariables& vars : ModuleInstanceVariables(design)) {
    ctx.RegisterScopeVariables(
        vars.scope,
        ScopeVariableSet{std::move(vars.prefix), std::move(vars.names)});
  }
  ctx.SetGlobalPrecision(design->global_time_precision);
  ctx.SetCompUnitTimeScale(design->cu_timescale);
  RegisterUnitTimeScales(design, ctx, ctx.GetArena());
  if (!design->top_modules.empty()) {
    const RtlirModule* top = design->top_modules.front();
    ctx.SetCurrentTimeScale(top->timescale);
    ctx.SetCurrentScopeName(top->name);
  }
  int finest = design->global_precision_order;
  for (auto* top : design->top_modules) {
    std::string below_top =
        top == design->top_modules.front() ? "" : std::string(top->name);
    RegisterScopeTimescales(top, ctx, std::string(top->name), below_top);
    finest = std::min(finest, FinestPrecisionOrder(top));
  }
  ctx.SetScopeTimeScale("$root", ScaleOfOrder(finest));
  for (const PackageDecl* pkg : design->packages) {
    ctx.SetScopeTimeScale(std::string(pkg->name) + "::",
                          PackageTimescale(*pkg, design->cu_timescale));
  }
}

void Lowerer::Lower(const RtlirDesign* design) {
  if (!design) return;
  if (design->simulation_blocked) return;
  design_ = design;
  VpiContext& vpi = GetGlobalVpiContext();
  interconnect_annotatable_ = DesignCallsSdfAnnotate(*design) ||
                              !vpi.RegisteredSystfs().empty() ||
                              !vpi.RegisteredCallbacks().empty();
  RegisterDesignScopes(design, ctx_);
  LowerDesignData();

  ctx_.GetScheduler().AddPostTimestepCallback(
      [ctx = &ctx_]() { ctx->AssertionSamples().Refill(ctx->GetArena()); });

  InitCompilationUnitData();
  LowerUnitClassPackageBases();
  LowerCompilationUnitClasses();
  RegisterFreeCuFunctions(design, ctx_, arena_);
  RegisterDesignScopeDpiImports(design, ctx_);
  const auto& tops = design->top_modules;
  if (!tops.empty()) ctx_.RegisterTopModule(tops.front()->name);
  ConstructDesignData();
  for (auto* mod : tops) {
    if (mod == tops.front()) {
      LowerModule(mod);
    } else if (!ctx_.IsParallelTop(mod->name)) {
      LowerParallelTop(mod);
    }
  }
  for (const auto& fill : deferred_param_fills_) fill();
  RegisterClassTypeAliases(design, ctx_, arena_);
  MakeNamedSpecializations();
  InitializeStaticLocals();

  AttachDesignClocking();
  AttachCodeCoverage(design, ctx_);
  LinkCheckerInstantiations();

  RegisterDesignAssertionSampling();

  RegisterDesignTiming();

  RegisterUnitLets(design, ctx_, arena_);

  if (DpiRuntime* dpi = ctx_.GetDpiRuntime(); dpi != nullptr) {
    ResolveDpiFormalTypes(*dpi, *design, ctx_);
  }

  AttachDesignToPliApplications(design, ctx_);

  CallBuildPeriodSystfRoutines(design, ctx_, arena_);

  vpi.DispatchCallbacks(kCbEndOfCompile);
  vpi.SetToolPhase(VpiToolPhase::kFull);
}

}  // namespace delta
