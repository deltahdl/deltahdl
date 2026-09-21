#include "simulator/lowerer.h"

#include <algorithm>
#include <cstdint>
#include <cstring>
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
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/assertion_read_names.h"
#include "simulator/awaiters.h"
#include "simulator/awaiters_event_control.h"
#include "simulator/class_object.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/expr_walk.h"
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
#include "simulator/timing_check_driver.h"
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

// §16.9.3: a sampled value function in a procedure is clocked by the
// procedure's event control, and the history it looks back through is
// sampled at every tick of that clock whether or not the statement holding
// the call is reached at the tick -- `$past(q)` written under an `if` still
// answers the tick before. The calls are collected once, and each is
// evaluated as the procedure resumes so that its sample for the tick is
// recorded; the evaluation where the statement is reached records the same
// value over it. $sampled looks back through nothing and is left out.
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
                                            SimContext& ctx, Arena& arena) {
  std::vector<const Expr*> past_sites = CollectPastDirectedSites(body);
  while (!ctx.StopRequested()) {
    co_await EventAwaiter{ctx, sens, arena};
    for (const Expr* site : past_sites) EvalExpr(site, ctx, arena);

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
  DropUnwatchableNames(ctx, read_vars);
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
      rvar->is_real = true;
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
      ctx_.Vcd().SetVcdVarKind(*full, DataTypeKind::kString);
      continue;
    }
    ParamStorageShape shape = ParamStorageShapeOf(p);
    uint32_t width = shape.width;
    auto* var = ctx_.CreateVariable(*full, width);
    var->value = MakeLogic4VecVal(arena_, width,
                                  static_cast<uint64_t>(p.resolved_value));
    // §6.20.2: a value wider than 64 bits is re-evaluated whole from its own
    // expression, the folded value holding the low word alone, as is one
    // whose expression holds an x or a z (§5.7.1), which the fold holds as 0.
    ReevaluateParamValue(p, var, ctx_, arena_);
    // §11.8.2: an operand is sign-extended to the propagated width only when it
    // is signed, so a parameter declared signed, or an untyped one whose final
    // value is (§6.20.2), has to reach evaluation carrying that. Without it
    // `parameter signed [3:0] P = -4'sd1` reads back as 15.
    var->is_signed = shape.is_signed;
    var->value.is_signed = shape.is_signed;
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

// A scope is recorded for the §30.3 specify blocks the module declares, for the
// §28.4 gate instantiations it declares, and for the §6.20.5 specparams it
// declares in its module body, because Lower registers all three from it. Any
// one of the three on its own is enough. §32.4.1 has a DEVICE entry fall back
// to the primitives driving an output when the module declares no specify path
// for it, so a module with gates and no specify block still has timing data an
// SDF file can annotate. A module that declares only a module-body specparam
// has no path and no gate for §32.4.3's LABEL annotation to rebuild, but the
// annotation still has work to do there:
// SpecifyManager::ApplyAnnotatedSpecparam writes the annotated value into the
// specparam's own storage, and §32.4.3 has every later evaluation of an
// expression containing that specparam -- a §9.4.1 delay control among them --
// read the annotated value back out of it. A module declaring none of the three
// is not recorded, having nothing for RegisterSpecifyBlocks,
// RegisterModuleGates or RegisterModuleSpecparams to walk.
void Lowerer::RecordSpecifyScope(const RtlirModule* mod) {
  if (mod->specify_blocks.empty() && mod->gate_insts.empty() &&
      mod->specparam_names.empty()) {
    return;
  }
  specify_scopes_.push_back(SpecifyScope{inst_prefix_, mod});
}

void Lowerer::LowerModule(const RtlirModule* mod) {
  RegisterInstanceKeyBinding(inst_prefix_, mod->library, mod->name, ctx_);
  LowerParams(mod);
  RecordSpecifyScope(mod);
  RegisterModuleNets(mod, ctx_, arena_);
  RegisterEnumTypes(mod);
  // §8.7/§6.8: class types must be registered before module variables so a
  // class-handle declaration with a `new` static initializer (e.g.
  // `C h = new(42);`) can construct its object during static initialization.
  // §8.9 (printed page 186) with §6.21 (printed 132-133): a static
  // property's one copy takes its initializer at the static initialization,
  // reading the declarations in scope, the module's variables among them,
  // so the initializers wait for those variables below
  // (InitClassStaticProperties); run here, with the classes' registration,
  // `module top; int K = 3; class C; static int s = K; static mailbox mb =
  // new(K); endclass` read K before LowerVar had given it 3: s was 0 and the
  // mailbox unbounded. A package's K was already right, ConstructDesignData
  // running ahead of every module.
  for (auto* cls : mod->class_decls) {
    RegisterClassDecl(cls, mod->function_decls);
  }
  // §6.8 sets a static variable's initial value as part of its declaration,
  // a reference the declaring scope makes, and §26.3 makes an import's names
  // visible throughout the importing scope, so the names the module's imports
  // bring in are bound before any variable's initializer is evaluated;
  // `import p1::*; int z = x;` read 0 while the binding came after the
  // variables. LowerImports leaves a name the module declares to the
  // declaration (§26.5). LowerChildModules orders an instance's the same way.
  LowerImports(mod);
  for (const auto& var : mod->variables) LowerVar(var.name, var);
  RegisterModulePorts(mod, ctx_, arena_);
  RegisterModuleSubroutines(mod, ctx_);
  for (auto* cls : mod->class_decls) InitClassStaticProperties(cls);
  // §23.6 with §13.3: a top-level module's subroutine enabled from a parallel
  // hierarchy is named through the top's name, `m.t1()` in the other top n,
  // so it is registered under that key as an instance's is under its prefix;
  // every top's bare names share one registry, so the key is what keeps m's
  // t1 apart from n's. FindSubroutineTarget in eval_function_hier.cpp runs
  // the body in the top's own instance, the one with no prefix.
  RegisterInstanceSubroutines(mod, std::string(mod->name) + ".", ctx_, arena_);
  // §27.4 with §13.4: a subroutine of one of the top's generate block
  // instances, `blk[1].triple()` from the top's own processes and
  // `m.blk[1].triple()` from a parallel top.
  RegisterGenBlockSubroutines(mod, inst_prefix_, inst_prefix_, ctx_, arena_);
  RegisterGenBlockSubroutines(mod, std::string(mod->name) + ".", inst_prefix_,
                              ctx_, arena_);
  RecordSubroutineAssertionSampleScopes(mod);
  // §35.5.4: an imported subroutine is declared where the source writes it and
  // called like a native one, so the declarations of the module being lowered
  // go into the registry EvalDpiCall reaches an import through.
  RegisterModuleDpiImports(mod, ctx_);
  RegisterModuleSequenceDecls(mod, ctx_);
  LowerSequenceMonitors(mod);

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

  // §14.3: the block's clock and signals are variables of this module, so it is
  // registered once they exist. AttachDesignClocking arms the watchers when the
  // whole design has been lowered.
  LowerClockingBlocks(mod);

  LowerChildModules(mod);
}

// §16.5.1: the variables a concurrent assertion's property reads are enrolled
// in the sampled-value store, so that the end of each time slot copies each
// one's value and the property is evaluated against that copy rather than
// against whatever stands at the clock tick. The functions below and those
// of simulator/assertion_read_names.h name what is enrolled;
// Lowerer::RegisterDesignAssertionSampling is where the enrolment happens.
//
// §16.9.3: "The use of these functions is not limited to assertion features;
// they may be used as expressions in procedural code as well." Each reads the
// sampled value of its argument, so the variables that argument names have to
// be enrolled wherever the call is written -- a `$sampled(x)` in a $display
// reads the store as much as one inside a property does, and a variable the
// store never heard of answers with its live value.
static bool IsSampledValueFunction(std::string_view name) {
  return name == "$sampled" || name == "$past" || name == "$rose" ||
         name == "$fell" || name == "$stable" || name == "$changed" ||
         IsGlobalClockingSampledFunction(name);
}

// The names read by the argument of every sampled value function call anywhere
// in `e`, which is the set those calls will ask the store for.
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

// The names the concurrent assertion `stmt` carries read: its boolean's
// operands and, §16.12.2, the names its flattened sequence reads, the
// sequences it instantiates included, which are read sampled as a boolean
// property is, and, §16.12.4 and §16.12.5, those of each operand of a
// property of operands.
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

// §16.14.6: a concurrent assertion embedded in procedural code is evaluated
// as a separate concurrent assertion is, on §16.5.1's sampled values, so the
// names each one in the procedure reads are enrolled as a static
// assertion's are.
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
    for (const Stmt* s : func->func_body_stmts) RecordAssertionSampleScope(s);
  }
}

void Lowerer::RegisterDesignAssertionSampling() {
  // §23.6 makes a hierarchical name an ordinary way to reach a variable, and
  // §16.5.1 puts no condition on where the variable a property reads is
  // declared, so `u.req` is enrolled exactly as a name the module declares
  // itself. That is why this runs after every module is lowered rather than
  // beside the process that named it: Lowerer::LowerChildModules creates an
  // instance's variables after the enclosing module's processes are lowered, so
  // a name resolved where it was found reached nothing and the read fell back
  // to the live value §16.5.1 exists to stop reading.
  //
  // Each name is resolved through SimContext::FindVariable under its own
  // instance prefix, which is the lookup the process body will make: no process
  // is executing here, so the prefix is the one SetLoweringInstancePrefix last
  // set, and the enrolled Variable* is therefore the one the read will find.
  for (const auto& scope : assertion_sample_scopes_) {
    ctx_.SetLoweringInstancePrefix(scope.inst_prefix);
    for (const auto& name : scope.names) {
      if (auto* var = ctx_.FindVariable(name)) {
        ctx_.AssertionSamples().Register(var, ctx_.GetArena());
      }
      // §16.6: a queue the property reads an element of is enrolled whole, so
      // the element read at a tick is the one sampled for it.
      if (auto* queue = ctx_.FindQueue(name)) {
        ctx_.AssertionSamples().RegisterQueue(queue, ctx_.GetArena());
      }
    }
  }
  ctx_.SetLoweringInstancePrefix("");
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
  // §16.5: the process carries a concurrent assertion's property, so it is
  // evaluated in the Observed region on the sampled values of the variables the
  // property names.
  p->is_concurrent_clocked = proc.is_concurrent_clocked;
  // §16.9.4: an attempt of a property naming one of the five future sampled
  // value functions is completed at the global clocking tick that follows its
  // own clock's, which is the event carried here.
  p->gclk_future_event = proc.gclk_future_event;
  // §16.9.3 has the sampled value functions "not limited to assertion
  // features", so the variables they name are enrolled wherever the call is
  // written and not only where a concurrent assertion's property stands. The
  // names are recorded here and resolved once the whole design is lowered,
  // because a property may name a variable of a child instance that does not
  // exist yet. A process naming none records nothing, which is every process in
  // a design that uses neither.
  RecordAssertionSampleScope(proc);
  // §18.14.1: a static process is seeded with the next value from the
  // initialization RNG of the enclosing instance. Lowering happens before any
  // thread runs, so the active stream here is the initialization RNG of the
  // instance being built, the one SetLoweringInstancePrefix last named.
  p->rng_seed = ctx_.DrawSeedForChild();
  p->gen_prefixes.assign(proc.gen_block_prefixes.begin(),
                         proc.gen_block_prefixes.end());
  p->gen_block_name = GenBlockName(proc.gen_block_path);
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

  // §16.14.6: the concurrent assertions the procedure embeds are evaluated
  // by monitors of their own, armed on their clocking events before the
  // procedure runs.
  StartProceduralAssertionMonitors(p, proc.body, ctx_, arena_);
  ScheduleProcess(p, ctx_);
}

// §20.4.1: publish each design element's resolved timescale under its module
// name and instance name so a $timeunit/$timeprecision argument that names the
// element (e.g. $timeunit(dut)) reports that element's value. Annex D.10 adds
// the element's complete hierarchical instance path, `from_top` starting at
// the top module's name and `below_top` starting under it, so a $scale
// argument that names a value through the instances above it, top.m1.l1.d or
// m1.l1.d, reaches the unit of the module holding the value, and the instance
// a process runs in is reached by the prefix the process carries.
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

// §3.12.1 (printed page 56) with §23.9 (printed 761): a function or task
// declared outside every module is nested in the compilation-unit scope,
// whose declarations its body reads by their bare names, never in the
// calling module's, so each is recorded as a subroutine of the unit's scope
// under the name the unit's storage is keyed by -- "$unit", kUnitScope in
// lowerer_package_data.cpp, which no package can be named, `$` starting no
// identifier -- as RegisterPackageScopedSubroutines (lowerer_register.cpp)
// records a package's; the call's frame then carries it
// (SimContext::EnterSubroutinePackage) and FindInPackageScope resolves a
// bare s to "$unit.s" ahead of the caller's. Registered under no scope, the
// unit's `function int len_s(); return s.len(); endfunction` beside a unit
// `string s = "unit"` read the calling top's own `string s` through the
// frame's fall-through to the instance's names, 12 for "modulestring", and
// its `s = "x"` wrote the top's s for the unit's.
static void RegisterFreeCuFunctions(const RtlirDesign* design,
                                    SimContext& ctx) {
  static constexpr std::string_view kUnitScope = "$unit";
  for (auto* item : design->cu_function_decls) {
    if (!item->method_class.empty()) continue;
    ctx.RegisterFunction(item->name, item);
    ctx.RegisterSubroutinePackage(item, kUnitScope);
  }
}

// §30.3, §32.4.1 and §6.20.5: the timing every module instance declared,
// registered into the manager the run reads. Separate from Lower because it is
// one step of it that grew its own paragraphs.
// §32.4.4: hands the manager the design's interconnect connectivity, without
// which an INTERCONNECT, PORT or NETDELAY entry has no ports, nets or
// primitives to look its names up in and annotates nothing at all. The
// connectivity is read off the parsed hierarchy rather than off the lowered
// design, because an interconnect delay has no SystemVerilog declaration behind
// it and §32.4.4's names are the design's own hierarchical names.
//
// The first top module is what is walked. §32.5's CELL records name an instance
// by a hierarchical path rooted at a top, and a design with two of them gives
// one path two readings, which is a question the SDF file cannot answer.
static void BindInterconnectTopology(const RtlirDesign* design,
                                     SpecifyManager& mgr) {
  if (design->compilation_unit == nullptr || design->top_decls.empty()) return;
  if (design->top_decls.front() == nullptr) return;
  mgr.BindDesignInterconnect(CollectInterconnectTopology(
      *design->compilation_unit, *design->top_decls.front()));
}

void Lowerer::RegisterDesignTiming() {
  // §30.3's specify block declares the design's specify data. The manager is
  // acquired whether or not any module declared a specify block, because
  // §32.9's $sdf_annotate reads timing data into it and has nowhere to put what
  // it reads without one -- EvalSdfAnnotateTask in
  // src/simulator/sdf_annotate_task.cpp returns immediately when
  // GetSpecifyManager is null. Registration comes after the modules are lowered
  // because a module path delay may be written as a specparam, and
  // RegisterSpecifyBlockSpecparams in
  // src/elaborator/elaborator_validate_specify.cpp lowers a specparam as a
  // variable of the module declaring it. Every module instance that declared a
  // specify block is registered under its own instance prefix, which is what
  // tells two instances of one cell apart, §30.4 having a specify block name
  // its terminals by the bare port names of the module it stands in. The
  // lowering instance prefix is set around each registration because a delay
  // written as a specparam is read back through SimContext::FindVariable, which
  // prepends SimContext::ActiveInstancePrefix; no process is running here, so
  // that prefix is the one SetLoweringInstancePrefix last set, and a specparam
  // of an instantiated module is reachable only while it names that instance.
  SpecifyManager& mgr = ctx_.AcquireSpecifyManager();
  BindInterconnectTopology(design_, mgr);
  for (const auto& scope : specify_scopes_) {
    ctx_.SetLoweringInstancePrefix(scope.inst_prefix);
    RegisterSpecifyBlocks(scope.module->specify_blocks, scope.inst_prefix, ctx_,
                          arena_, mgr);
    // §32.4.1: the primitives driving a module output are what a DEVICE entry
    // annotates when the module declares no specify path for that output, so
    // the gate instantiations are registered beside the specify blocks. They
    // are registered here rather than where LowerModule rewrote them into
    // continuous assignments for the reason the specify blocks are: a gate's
    // propagation delay may be written as a specparam, and it is evaluated
    // under the same lowering instance prefix so that
    // SimContext::FindVariable reaches the specparam of this instance.
    RegisterModuleGates(scope.module->gate_insts, scope.inst_prefix, ctx_,
                        arena_, mgr);
    // §6.20.5 admits two declaration sites for a specparam -- "inside a specify
    // block or in the module body" -- and §32.4.3 states no exception for
    // either, so the module-body ones are bound beside the in-block ones
    // RegisterSpecifyBlocks binds. Only the name has to be bound: the storage
    // the annotated value lands in was lowered above, because
    // Elaborator::ElaborateSpecparam (src/elaborator/elaborator_items.cpp)
    // makes the declaration a variable of the module declaring it, which
    // Lowerer::LowerModule lowers for a top and
    // Lowerer::CreateChildModuleVariables lowers under the instance prefix for
    // an instantiated module.
    RegisterModuleSpecparams(scope.module->specparam_names, scope.inst_prefix,
                             ctx_, arena_, mgr);
  }
  ctx_.SetLoweringInstancePrefix("");
  // §30.5.3 selects among the module paths "whose input has transitioned most
  // recently in time", and nothing records when a signal last changed. This
  // arms the watcher that does, on the source terminal of every path just
  // registered, before the scheduler runs anything -- a source that transitions
  // before it is watched leaves no time behind for the selection to read.
  WatchModulePathSources(mgr, ctx_);
  // §31.3 reports a timing violation when the data signal transitions inside
  // the window the reference signal defines, and nothing watches the two
  // signals a registered check names. This arms the watchers that do, on the
  // $setup and $hold checks just registered and before the scheduler runs
  // anything -- a signal that transitions before it is watched leaves no
  // transition behind for the check to measure.
  WatchTimingChecks(mgr, ctx_);
}

// Annex D.11: the interactive scope consulted by the optional $scope system
// task starts at the first top-level module, and a later $scope call retargets
// it to one of the scopes registered here, each by its complete hierarchical
// name.
static void RegisterInteractiveScopes(const RtlirDesign* design,
                                      SimContext& ctx) {
  if (!design->top_modules.empty()) {
    ctx.SetInteractiveScope(design->top_modules.front()->name);
  }
  for (const std::string& name : CompleteHierarchicalScopeNames(design)) {
    ctx.RegisterHierarchicalScope(name);
  }
  // Annex D.13: the reg and net variables $showvars reports for a module
  // instance, under the instance's complete hierarchical name.
  for (ScopeDeclaredVariables& vars : ModuleInstanceVariables(design)) {
    ctx.RegisterScopeVariables(
        vars.scope,
        ScopeVariableSet{std::move(vars.prefix), std::move(vars.names)});
  }
}

// §3.12.1: the unit's imports are visible to its own class declarations and
// to every module, and §26.5 has a declaration of the scope take the name
// over an import, so the imports bind first (InitCompilationUnitData, which
// Lower runs ahead of this) and a unit class rebinds its name over them; the
// first of two unit classes of one name keeps it.
void Lowerer::LowerCompilationUnitClasses() {
  std::unordered_set<std::string_view> unit_class_names;
  for (auto* cls : design_->cu_class_decls) {
    if (unit_class_names.insert(cls->name).second)
      LowerClassDecl(cls, design_->cu_function_decls);
  }
}

void Lowerer::Lower(const RtlirDesign* design) {
  if (!design) return;
  // §20.10.1: a $fatal or $error elaboration severity task that survived
  // generate expansion marks the design as not startable. Refuse to lower
  // any part of it so the scheduler sees an empty event calendar.
  if (design->simulation_blocked) return;
  design_ = design;
  RegisterInteractiveScopes(design, ctx_);
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
    RegisterScopeTimescales(top, ctx_, std::string(top->name), "");
  }
  LowerDesignData();

  // §16.5.1 reads a concurrent assertion's variables as of the Preponed region
  // of the time slot the clock tick falls in. No event reaches a Preponed
  // region -- the scheduler drains it once, ahead of the iterative regions, and
  // never returns to it -- and §4.4.2.1 makes that unnecessary: "Sampling in
  // the Preponed region is equivalent to sampling in the previous Postponed
  // region." The sample is therefore taken once a time slot has finished, where
  // it is the next slot's Preponed value. Registering it here rather than
  // beside the first assertion keeps it to one registration per run; it does
  // nothing while no assertion has enrolled a variable.
  ctx_.GetScheduler().AddPostTimestepCallback(
      [ctx = &ctx_]() { ctx->AssertionSamples().Refill(ctx->GetArena()); });

  InitCompilationUnitData();
  LowerCompilationUnitClasses();
  RegisterFreeCuFunctions(design, ctx_);
  RegisterDesignScopeDpiImports(design, ctx_);
  // §23.6: each top-level module roots a name hierarchy, and a path from a
  // parallel hierarchy starts at its name; every top's name is recorded
  // ahead of any lowering so a top's declaration initializer can already
  // name another top.
  for (auto* top : design->top_modules) ctx_.RegisterTopModule(top->name);
  // §26.2 with §6.21: the packages' and the unit's objects exist before the
  // first module's declaration initializer runs (lowerer_data_init.cpp).
  ConstructDesignData();
  for (auto* mod : design->top_modules) {
    LowerModule(mod);
  }
  // §26.3: the bare names of the package classes no scope had bound, held
  // back while the modules bound their own, and the typedef names that
  // denote one of them (§6.18), bound once the modules are lowered.
  RebindStrayPackageClassNames();
  RegisterClassTypeAliases(design, ctx_);

  AttachDesignClocking();

  RegisterDesignAssertionSampling();

  RegisterDesignTiming();

  for (auto* let_decl : design->cu_let_decls) {
    ctx_.RegisterLetDecl(let_decl->name, let_decl);
  }

  // §36.6: the design is put within reach of the PLI applications here, ahead
  // of the build period below and of every event after it, because a routine
  // called in either period is one of the "C language functions that utilize
  // the library of PLI C functions to access and interact dynamically with
  // SystemVerilog software implementations".
  AttachDesignToPliApplications(design, ctx_);

  // §36.8: the simulation data structure is built by the time this returns, so
  // this is the period §36.8.1's sizetf and §36.8.2's compiletf are called in
  // -- last of everything the build does, and before the scheduler runs an
  // event.
  CallBuildPeriodSystfRoutines(design, ctx_, arena_);

  // §38.36.3: "cbEndOfCompile -- end of simulation data structure compilation
  // or build", which is here: the structure is built and the build period's
  // routines have run. §36.10.2 puts it in the same place and says what it
  // opens -- "after the sizetf routines are called, the routines registered for
  // reason cbEndOfCompile are called. At this point, and continuing until the
  // tool has finished execution, all functionality is available" -- so the
  // phase moves with it.
  VpiContext& vpi = GetGlobalVpiContext();
  vpi.DispatchCallbacks(kCbEndOfCompile);
  vpi.SetToolPhase(VpiToolPhase::kFull);
}

}  // namespace delta
