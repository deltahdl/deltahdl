#include "simulator/lowerer.h"

#include <algorithm>
#include <cstring>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/awaiters.h"
#include "simulator/class_object.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_child.h"
#include "simulator/lowerer_register.h"
#include "simulator/net.h"
#include "simulator/process.h"
#include "simulator/sequence_monitor.h"
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
    // §16.4.2: resuming after suspending on this event control is a deferred
    // assertion flush point; discard reports pending from before the suspend.
    ctx.FlushPendingDeferredReports();
    auto result = co_await ExecStmt(body, ctx, arena);
    if (result != StmtResult::kDone) break;
  }
}

// §9.2.2.2: a variable passed to an output formal of a called task/function is
// written by the call, not read. It must stay out of an always_comb's implicit
// sensitivity list; otherwise the block re-triggers on its own write and spins
// in a zero-delay loop. An inout actual is read as well as written, so only
// pure outputs are excluded. Callee formals come from the runtime subroutine
// registry, which is populated (RegisterModuleSubroutines) before processes are
// lowered.
// Records the base identifiers of any output actuals of a single call node.
static void CollectOutputActualsOfCall(const Expr* call, SimContext& ctx,
                                       std::unordered_set<std::string>& out) {
  const ModuleItem* fn = ctx.FindFunction(call->callee);
  if (!fn) return;
  size_t n = std::min(call->args.size(), fn->func_args.size());
  for (size_t i = 0; i < n; ++i) {
    if (fn->func_args[i].direction != Direction::kOutput) continue;
    const Expr* a = call->args[i];
    while (a && a->kind == ExprKind::kSelect && a->base) a = a->base;
    if (a && a->kind == ExprKind::kIdentifier && !a->text.empty())
      out.insert(std::string(a->text));
  }
}

static void CollectCallOutputActuals(const Expr* expr, SimContext& ctx,
                                     std::unordered_set<std::string>& out) {
  if (!expr) return;
  if (expr->kind == ExprKind::kCall && !expr->callee.empty())
    CollectOutputActualsOfCall(expr, ctx, out);
  CollectCallOutputActuals(expr->lhs, ctx, out);
  CollectCallOutputActuals(expr->rhs, ctx, out);
  CollectCallOutputActuals(expr->condition, ctx, out);
  CollectCallOutputActuals(expr->true_expr, ctx, out);
  CollectCallOutputActuals(expr->false_expr, ctx, out);
  CollectCallOutputActuals(expr->base, ctx, out);
  CollectCallOutputActuals(expr->index, ctx, out);
  for (auto* arg : expr->args) CollectCallOutputActuals(arg, ctx, out);
  for (auto* elem : expr->elements) CollectCallOutputActuals(elem, ctx, out);
}

static void CollectCallOutputActuals(const Stmt* stmt, SimContext& ctx,
                                     std::unordered_set<std::string>& out) {
  if (!stmt) return;
  CollectCallOutputActuals(stmt->condition, ctx, out);
  CollectCallOutputActuals(stmt->rhs, ctx, out);
  CollectCallOutputActuals(stmt->expr, ctx, out);
  CollectCallOutputActuals(stmt->for_cond, ctx, out);
  CollectCallOutputActuals(stmt->assert_expr, ctx, out);
  for (auto* s : stmt->stmts) CollectCallOutputActuals(s, ctx, out);
  CollectCallOutputActuals(stmt->then_branch, ctx, out);
  CollectCallOutputActuals(stmt->else_branch, ctx, out);
  CollectCallOutputActuals(stmt->for_body, ctx, out);
  for (auto* fi : stmt->for_inits) CollectCallOutputActuals(fi, ctx, out);
  for (auto* fs : stmt->for_steps) CollectCallOutputActuals(fs, ctx, out);
  CollectCallOutputActuals(stmt->body, ctx, out);
  for (auto* s : stmt->fork_stmts) CollectCallOutputActuals(s, ctx, out);
  for (const auto& ci : stmt->case_items)
    CollectCallOutputActuals(ci.body, ctx, out);
}

static SimCoroutine MakeAlwaysCombCoroutine(const Stmt* body,
                                            const std::vector<EventExpr>& sens,
                                            SimContext& ctx, Arena& arena) {
  // §9.2.2.2.1: always_comb/always_latch watch the inferred sensitivity list,
  // which (unlike a raw read scan of the body) descends into called functions
  // and reduces each read to its base signal name -- so a variable read only
  // inside a called function still re-triggers the block, and a bit-select read
  // watches the whole vector. proc.sensitivity already excludes block-locals
  // and self-written signals; additionally drop any variable passed to a called
  // subroutine's output formal -- it is written by the call, not read, and
  // would otherwise re-trigger the block on its own update (a zero-delay spin).
  std::unordered_set<std::string> call_outputs;
  CollectCallOutputActuals(body, ctx, call_outputs);
  std::vector<std::string_view> read_vars;
  read_vars.reserve(sens.size());
  for (const auto& ev : sens) {
    if (!ev.signal || ev.signal->text.empty()) continue;
    if (call_outputs.count(std::string(ev.signal->text)) != 0) continue;
    read_vars.push_back(ev.signal->text);
  }
  while (!ctx.StopRequested()) {
    co_await ExecStmt(body, ctx, arena);
    if (read_vars.empty()) break;
    co_await AnyChangeAwaiter{ctx, read_vars};

    ctx.FlushPendingViolations();
    // §16.4.2: an always_comb/always_latch procedure re-running because a
    // dependent signal changed reaches a deferred assertion flush point on
    // resume, clearing any report queued by the superseded evaluation.
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
    // §23.10/§6.20: a parameter is an instance-specific runtime value, so its
    // variable is scoped by the instance prefix (empty for a top module). This
    // makes a child instance's parameters — including any defparam override —
    // visible to that instance's processes. The name is arena-persisted because
    // SimContext keys variables by string_view.
    auto* full = arena_.Create<std::string>(inst_prefix_ + std::string(p.name));
    if (p.is_unbounded) {
      ctx_.RegisterUnboundedParam(*full);
      ctx_.CreateVariable(*full, 32);
      continue;
    }
    if (!p.is_resolved) continue;
    // §6.20.2: a parameter declared real holds a real value, so it is lowered
    // the way a real variable is -- the double's bit pattern in 64 bits, marked
    // real and registered as one. Everything that reads a real reads it from
    // that mark, so without it the same 64 bits are taken for the integer they
    // spell.
    if (p.is_real_value) {
      auto* rvar = ctx_.CreateVariable(*full, 64);
      uint64_t bits = 0;
      std::memcpy(&bits, &p.resolved_real, sizeof(bits));
      rvar->value = MakeLogic4VecVal(arena_, 64, bits);
      rvar->value.is_real = true;
      ctx_.RegisterRealVariable(*full);
      continue;
    }
    // §6.16: a parameter declared string holds a value of arbitrary length, and
    // the subclause rules that for it "no truncation occurs". Neither half of
    // the lowering below can honour that. EvalTypeWidth gives kString no width,
    // so decl_width is 0 and the fallback takes 32, keeping four characters of
    // the ten in §6.16's own example `parameter string default_name = "John
    // Smith"`; and resolved_value is 64 bits, which is why the characters are
    // read from resolved_string instead. StringToLogic4Vec packs one byte per
    // character with the leftmost character in the most significant byte, and
    // StripStringZeros drops the "\0" §6.16 forbids a string to contain,
    // leaving a value exactly as wide as the characters need. Registering the
    // variable as a string is the same second half the real arm above has,
    // because what reads a string reads SimContext::IsStringVariable rather
    // than the width.
    //
    // An overridden parameter is read here too, because is_string_value being
    // set says resolved_string holds the value the parameter has now rather
    // than the one it was declared with. ApplyParamOverride records the
    // characters for §23.10.2's two instance forms and for a configuration, on
    // a parameter whose is_string_value is still clear and whose declared
    // initializer Elaborator::ElaborateParamPortList then withholds; an
    // override that is not a string literal therefore leaves the flag clear.
    // Elaborator::ApplyDefparams records them for §23.10.1's defparam, where
    // the declaration's own characters are already recorded by then, so it
    // clears the flag itself when the right-hand side is not a string literal.
    if (p.is_string_value) {
      auto chars = StripStringZeros(
          StringToLogic4Vec(arena_, p.resolved_string), arena_);
      auto* svar = ctx_.CreateVariable(*full, chars.width);
      svar->value = chars;
      ctx_.RegisterStringVariable(*full);
      // §21.7.5: Table 21-11 gives string no row, and §21.7.2.3 rules that a
      // $var's size "specifies how many bits are in the variable", which no
      // size states for a value whose length §6.16 lets vary. SimContext
      // decides that by the declared kind, so without this the parameter is
      // dumped with a $var size that follows its character count.
      ctx_.SetVcdVarKind(*full, DataTypeKind::kString);
      continue;
    }
    // Use declared width if parameter has explicit type, else 32 (§10.8
    // context)
    uint32_t width = (p.decl_width > 0) ? p.decl_width : 32;
    auto* var = ctx_.CreateVariable(*full, width);
    var->value = MakeLogic4VecVal(arena_, width,
                                  static_cast<uint64_t>(p.resolved_value));
    // §11.8.2: an operand is sign-extended to the propagated width only when it
    // is signed, so a parameter declared signed has to reach evaluation
    // carrying that. Without it `parameter signed [3:0] P = -4'sd1` reads back
    // as 15.
    var->is_signed = p.decl_is_signed;
    var->value.is_signed = p.decl_is_signed;
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
        // §10.11: aliased nets denote the same physical net, so they share one
        // resolved storage. Redirect both the variable map (used for reads) and
        // the net map (used by continuous-assign driver resolution); otherwise
        // a driver on the non-primary net writes a Variable the alias never
        // sees.
        ctx_.AliasVariable(net->text, primary);
        ctx_.AliasNet(net->text, primary);
      }
    }
  }
}

void RegisterInstanceKeyBinding(const std::string& inst_prefix,
                                std::string_view library, std::string_view name,
                                SimContext& ctx) {
  std::string key = inst_prefix;
  if (!key.empty() && key.back() == '.') key.pop_back();
  ctx.RegisterInstanceType(key, name);
  // §33.7: record this instance's resolved library.cell so the %l/%L display
  // specifier can report its binding. The cell is the module's design-element
  // name; the library is the one it was compiled into.
  ctx.RegisterInstanceBinding(key, library, name);
}

void Lowerer::LowerModule(const RtlirModule* mod) {
  RegisterInstanceKeyBinding(inst_prefix_, mod->library, mod->name, ctx_);
  LowerParams(mod);
  RegisterModuleNets(mod, ctx_, arena_);
  RegisterEnumTypes(mod);
  // §8.7/§6.8: class types must be registered before module variables so a
  // class-handle declaration with a `new` static initializer (e.g.
  // `C h = new(42);`) can construct its object during static initialization.
  for (auto* cls : mod->class_decls) {
    LowerClassDecl(cls);
  }
  for (const auto& var : mod->variables) LowerVar(var.name, var);
  RegisterModulePorts(mod, ctx_, arena_);
  RegisterModuleSubroutines(mod, ctx_);
  RegisterModuleSequenceDecls(mod, ctx_);
  LowerSequenceMonitors(mod);

  LowerImports(mod);
  RegisterProcessClassType(ctx_, arena_);
  LowerAliases(mod);
  uint32_t program_block_id = mod->is_program ? next_program_block_id_++ : 0;
  LowerProcesses(mod->processes, mod->is_program, program_block_id);
  for (const auto& ca : mod->assigns) {
    LowerContAssign(ca, mod->is_program);
  }
  // §29.8: "Instances of UDPs are specified inside modules in the same manner
  // as gates", so a primitive instance is lowered beside the continuous
  // assignments a gate instance elaborates to.
  for (const auto& udp_inst : mod->udp_insts) {
    LowerUdpInst(udp_inst, mod->is_program);
  }

  LowerChildModules(mod);
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
  p->gen_prefixes.assign(proc.gen_block_prefixes.begin(),
                         proc.gen_block_prefixes.end());
  InstallGenBlockConsts(proc.gen_block_consts, p);

  // §16.4.4: a `disable` naming the outermost scope of a procedure flushes its
  // pending deferred assertion reports even while that procedure sits suspended
  // on its event control, so the label is recorded for the life of the process
  // rather than left to the registration the block makes and takes back.
  if (proc.body != nullptr && proc.body->kind == StmtKind::kBlock &&
      !proc.body->label.empty()) {
    ctx_.RegisterOutermostScope(proc.body->label, p);
  }

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
      p->coro =
          MakeAlwaysCombCoroutine(proc.body, proc.sensitivity, ctx_, arena_)
              .Release();
      break;
    case RtlirProcessKind::kAlwaysFF:
      // §9.2.2.4: an always_ff is driven by its explicit edge event control
      // (stored in proc.sensitivity), so it must wait on that event each
      // iteration like a sensitized always. Using the always_comb re-trigger
      // loop instead made it re-fire on its own nonblocking-assign updates and
      // spin forever.
      p->kind = ProcessKind::kAlwaysFF;
      p->coro =
          MakeAlwaysSensCoroutine(proc.body, proc.sensitivity, ctx_, arena_)
              .Release();
      break;
    case RtlirProcessKind::kFinal:
      p->kind = ProcessKind::kFinal;
      p->coro = MakeInitialCoroutine(proc.body, ctx_, arena_).Release();
      ctx_.RegisterFinalProcess(p);
      return;
  }

  ScheduleProcess(p, ctx_);
}

// §16.13.6/§9.4.4: spawn a monitor process for each named sequence whose simple
// clocked linear body the parser captured, so its endpoint event fires on a
// match and procedural `sequence.triggered`/`wait` observe it. Additive: no
// other code fires these endpoint events.
void Lowerer::LowerSequenceMonitors(const RtlirModule* mod) {
  for (auto* seq : mod->sequence_decls) {
    if (seq->seq_clock.empty() || seq->seq_linear_operands.empty()) continue;
    auto* p = arena_.Create<Process>();
    p->kind = ProcessKind::kAlways;
    p->id = next_id_++;
    p->home_region = Region::kActive;
    p->inst_prefix = inst_prefix_;
    p->rng_seed = ctx_.DrawSeedForChild();
    p->coro = MakeSequenceMonitorCoroutine(seq, ctx_, arena_).Release();
    ScheduleProcess(p, ctx_);
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

// §20.4.1: publish each design element's resolved timescale under its module
// name and instance name so a $timeunit/$timeprecision argument that names the
// element (e.g. $timeunit(dut)) reports that element's value.
static void RegisterScopeTimescales(const RtlirModule* mod, SimContext& ctx) {
  ctx.SetScopeTimeScale(mod->name, mod->timescale);
  for (const auto& child : mod->children) {
    if (!child.resolved) continue;
    ctx.SetScopeTimeScale(child.inst_name, child.resolved->timescale);
    RegisterScopeTimescales(child.resolved, ctx);
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
    // 8.24: the out-of-block definition repeats neither the lifetime nor the
    // static qualifier, so the body item parses with is_static false. Carry the
    // static-ness forward from the in-class prototype before the body replaces
    // it, so a class-scoped call (C#()::f()) still resolves it as static.
    auto existing = cls->methods.find(name);
    if (existing != cls->methods.end() && existing->second->is_static) {
      item->is_static = true;
    }
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
  // §20.4.1 / §3.14.3: seed the runtime timescale state read by
  // $timeunit/$timeprecision. The simulation time unit and compilation-unit
  // timescale come from the design; the top module is the initial current
  // scope reported when those functions take no argument.
  ctx_.SetGlobalPrecision(design->global_time_precision);
  ctx_.SetCompUnitTimeScale(design->cu_timescale);
  if (!design->top_modules.empty()) {
    const RtlirModule* top = design->top_modules.front();
    ctx_.SetCurrentTimeScale(top->timescale);
    ctx_.SetCurrentScopeName(top->name);
  }
  for (auto* top : design->top_modules) {
    RegisterScopeTimescales(top, ctx_);
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
