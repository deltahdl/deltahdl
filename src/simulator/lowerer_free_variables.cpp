#include <algorithm>
#include <cstddef>
#include <functional>
#include <map>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"
#include "simulator/assertion_read_names.h"
#include "simulator/assume_obligations.h"
#include "simulator/awaiters_event_control.h"
#include "simulator/eval_function_internal.h"
#include "simulator/expr_walk.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sva_engine_sampling.h"

namespace delta {

namespace {

// One assumption of a checker instance's assume set, written in the terms of
// the instance whose free variables it constrains: the clock it is evaluated
// on, in the scope `clock_prefix` names; the obligation each of its attempts
// begins with and those of its attempts in flight; and its disable
// condition.
struct AssumeSetMember {
  std::string clock_prefix;
  std::vector<EventExpr> clock;
  const ObligationNode* begin = nullptr;
  std::vector<const ObligationNode*> live;
  Expr* disable = nullptr;
  bool fired = false;
};

// The assume set of a checker instance: `args` names the active free
// variables a solution attempt draws, `scope` is the process whose scope and
// random stream it draws them in, and `solves` holds the scope randomize call
// made for each set of conditions an attempt has been held to.
struct AssumeSet {
  AssumeSet(SimContext& ctx, Arena& arena) : obligations(ctx, arena) {}
  AssumeObligations obligations;
  std::vector<AssumeSetMember> members;
  std::vector<Expr*> args;
  Process* scope = nullptr;
  bool scheduled = false;
  std::map<std::vector<Expr*>, Expr*> solves;
};

Expr* NameExpr(std::string_view name, Arena& arena) {
  auto* id = arena.Create<Expr>();
  id->kind = ExprKind::kIdentifier;
  id->text = name;
  return id;
}

Expr* RandomizeCall(const std::vector<Expr*>& args, ClassMember* constraints,
                    Arena& arena) {
  auto* call = arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->lhs = NameExpr("randomize", arena);
  call->inline_constraint = constraints;
  call->args = args;
  return call;
}

// §16.12.1: the members that ticked and whose disable condition holds drop
// their attempts in flight and begin none.
void DropDisabled(AssumeSet& set) {
  for (AssumeSetMember& m : set.members) {
    if (m.fired && m.disable != nullptr && set.obligations.Holds(m.disable)) {
      m.live.clear();
      m.fired = false;
    }
  }
}

// The scope randomize call an attempt makes over the conditions under which
// no attempt in flight of a member that ticked fails, a new one begun among
// them.
Expr* SolveFor(AssumeSet& set, Arena& arena) {
  std::vector<Expr*> key;
  for (AssumeSetMember& m : set.members) {
    if (!m.fired) continue;
    m.live.push_back(m.begin);
    for (const ObligationNode* node : m.live) {
      Expr* cond = set.obligations.NoFailCondition(node);
      if (cond != nullptr) key.push_back(cond);
    }
  }
  std::ranges::sort(key);
  auto [first, last] = std::ranges::unique(key);
  key.erase(first, last);
  Expr*& solve = set.solves[key];
  if (solve != nullptr) return solve;
  auto* constraints = arena.Create<ClassMember>();
  constraints->constraint_exprs = key;
  solve = RandomizeCall(set.args, constraints, arena);
  return solve;
}

// Each attempt in flight of a member that ticked steps past this tick, the
// values the attempt drew read, and leaves once it owes nothing more.
void StepMembers(AssumeSet& set) {
  set.obligations.NewTimeStep();
  for (AssumeSetMember& m : set.members) {
    if (!m.fired) continue;
    std::vector<const ObligationNode*> live;
    for (const ObligationNode* node : m.live) {
      const ObligationNode* next = set.obligations.Step(node);
      if (!set.obligations.Settled(next)) live.push_back(next);
    }
    std::ranges::sort(live);
    auto [first, last] = std::ranges::unique(live);
    live.erase(first, last);
    m.live = std::move(live);
    m.fired = false;
  }
}

// §17.7.2: a solution attempt, made before the Observed region, reads every
// other variable at its sampled value and each active free variable at its
// current one, which the sampling store answers for it.
void AttemptSolution(AssumeSet& set, SimContext& ctx, Arena& arena) {
  Process* saved = ctx.CurrentProcess();
  ctx.SetCurrentProcess(set.scope);
  ctx.AssertionSamples().SetEvaluatingProperty(true);
  set.obligations.NewTimeStep();
  DropDisabled(set);
  Logic4Vec drawn;
  TryEvalScopeRandomizeCall(SolveFor(set, arena), ctx, arena, drawn);
  StepMembers(set);
  ctx.AssertionSamples().SetEvaluatingProperty(false);
  ctx.SetCurrentProcess(saved);
  set.scheduled = false;
}

// §17.7.2: one solution attempt in the Pre-Observed region of the time step,
// whichever assume set clock event, or how many, called for it.
void RequestSolutionAttempt(AssumeSet& set, SimContext& ctx, Arena& arena) {
  if (set.scheduled) return;
  set.scheduled = true;
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->callback = [&set, &ctx, &arena]() {
    AttemptSolution(set, ctx, arena);
  };
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kPreObserved,
                                   event);
}

// §17.7.2: the clock of the assumption `set.members[i]` is one of the clock
// events of the assume set, each of which triggers a solution attempt.
SimCoroutine MakeAssumeClockCoroutine(AssumeSet& set, size_t i, SimContext& ctx,
                                      Arena& arena) {
  AssumeSetMember& m = set.members[i];
  while (!ctx.StopRequested()) {
    co_await EventAwaiter{ctx, m.clock, arena};
    m.fired = true;
    RequestSolutionAttempt(set, ctx, arena);
  }
}

std::unordered_set<std::string> ReadNames(const std::vector<Expr*>& reads) {
  std::unordered_set<std::string> names;
  for (const Expr* e : reads) CollectSampledOperandNames(e, names);
  return names;
}

bool ReadsAny(const std::vector<Expr*>& reads,
              const std::unordered_set<std::string>& names) {
  return std::ranges::any_of(ReadNames(reads), [&](const std::string& n) {
    return names.count(n) != 0;
  });
}

// §17.7.2 with §17.3: the formals of the instance `self` whose actual holds a
// const cast or an automatic value of the procedure instantiating it.
std::unordered_set<std::string> BarredFormals(const RtlirModuleInst& self) {
  std::unordered_set<std::string_view> automatics(
      self.procedure_automatics.begin(), self.procedure_automatics.end());
  std::unordered_set<std::string> barred;
  for (const RtlirPortBinding& binding : self.port_bindings) {
    ForEachSubExpr(binding.connection, [&](const Expr* sub) {
      if ((sub->kind == ExprKind::kCast && sub->text == "const") ||
          (sub->kind == ExprKind::kIdentifier &&
           automatics.count(sub->text) != 0)) {
        barred.insert(std::string(binding.port_name));
      }
    });
  }
  return barred;
}

// An assumption the assume set may hold: its process, the scope its clock
// is read in, the rewrite into the terms of the checker the set is
// collected for, and the expressions it reads in those terms.
struct Candidate {
  const RtlirProcess* proc = nullptr;
  std::string clock_prefix;
  ObligationRewrite rewrite;
  std::vector<Expr*> reads;
};

// §17.7.2: the assumptions of the checker `mod`, lowered under `prefix`, and
// those of its child checkers, each in `mod`'s terms, a child's formals
// replaced by its actuals; of them, one that reads a formal the instance
// `self` binds to a const cast or an automatic value is left out, and so is
// one of a form the obligations do not model.
std::vector<Candidate> CollectAssumptions(const RtlirModule* mod,
                                          const std::string& prefix,
                                          const RtlirModuleInst& self,
                                          AssumeObligations& obligations,
                                          Arena& arena) {
  std::vector<Candidate> out;
  for (const RtlirProcess& proc : mod->processes) {
    if (!proc.is_concurrent_clocked ||
        proc.body->kind != StmtKind::kAssumeImmediate) {
      continue;
    }
    Candidate c{&proc, prefix, [](Expr* e) { return e; }, {}};
    if (obligations.Begin(proc.body, c.rewrite, c.reads) != nullptr) {
      out.push_back(std::move(c));
    }
  }
  // §17.2: a checker instantiates no other kind of definition.
  for (const RtlirModuleInst& child : mod->children) {
    ActualsByFormal actuals;
    for (const RtlirPortBinding& binding : child.port_bindings) {
      actuals[binding.port_name] = binding.connection;
    }
    for (Candidate& c : CollectAssumptions(
             child.resolved, prefix + std::string(child.inst_name) + ".", child,
             obligations, arena)) {
      for (Expr*& read : c.reads)
        read = SubstituteFormals(read, actuals, arena);
      c.rewrite = [rewrite = std::move(c.rewrite), actuals, &arena](Expr* e) {
        return SubstituteFormals(rewrite(e), actuals, arena);
      };
      out.push_back(std::move(c));
    }
  }
  const std::unordered_set<std::string> kBarred = BarredFormals(self);
  std::erase_if(out,
                [&](const Candidate& c) { return ReadsAny(c.reads, kBarred); });
  return out;
}

// §17.7.2: the assume set's members, the assumptions of `candidates` that
// read one of the active free variables `active`.
void AddMembers(const std::vector<Candidate>& candidates,
                const std::unordered_set<std::string>& active, AssumeSet& set) {
  for (const Candidate& c : candidates) {
    if (!ReadsAny(c.reads, active)) continue;
    AssumeSetMember m;
    m.clock_prefix = c.clock_prefix;
    m.clock = c.proc->sensitivity;
    std::vector<Expr*> reads;
    m.begin = set.obligations.Begin(c.proc->body, c.rewrite, reads);
    Expr* disable = c.proc->body->assert_disable_iff;
    if (disable != nullptr) m.disable = c.rewrite(disable);
    set.members.push_back(std::move(m));
  }
}

}  // namespace

// §17.7.2: every free variable of a checker instance whose declaration
// writes no initializer starts at an unconstrained random value, drawn from
// the instance's initialization stream. Its active free variables are then
// assigned, at each clock event of its assume set, values with which no
// attempt in flight of the assumptions of the set that ticked fails at that
// tick, a new attempt of each begun there among them, found by §18.12's
// scope randomize over them with the conditions under which none fails as
// its constraints; the other variables the conditions read stand at their
// sampled values. The set holds the instance's assumptions and its child
// checkers' that read one of its active free variables; where it holds none,
// the attempt is made, unconstrained, at every time step. An active free
// variable is read at its current value, which §17.7.2 makes its sampled
// value, so it is kept out of the sampling store.
void Lowerer::LowerFreeVariableSolver(const RtlirModule* mod) {
  if (!mod->random_initial_variables.empty()) {
    std::vector<Expr*> initial;
    initial.reserve(mod->random_initial_variables.size());
    for (std::string_view name : mod->random_initial_variables) {
      initial.push_back(NameExpr(name, arena_));
    }
    Logic4Vec drawn;
    TryEvalScopeRandomizeCall(RandomizeCall(initial, nullptr, arena_), ctx_,
                              arena_, drawn);
  }
  if (mod->free_variables.empty()) return;
  auto* set = arena_.Create<AssumeSet>(ctx_, arena_);
  std::unordered_set<std::string> active;
  for (std::string_view name : mod->free_variables) {
    active.emplace(name);
    set->args.push_back(NameExpr(name, arena_));
    ctx_.AssertionSamples().ExcludeFromSampling(ctx_.FindVariable(name));
  }
  AddMembers(CollectAssumptions(mod, inst_prefix_, *lowering_inst_,
                                set->obligations, arena_),
             active, *set);
  set->scope = arena_.Create<Process>();
  set->scope->inst_prefix = inst_prefix_;
  set->scope->rng_seed = ctx_.DrawSeedForChild();
  if (set->members.empty()) {
    ctx_.GetScheduler().AddTimeSlotStartCallback(
        [set, &ctx = ctx_, &arena = arena_]() {
          RequestSolutionAttempt(*set, ctx, arena);
        });
    return;
  }
  for (size_t i = 0; i < set->members.size(); ++i) {
    auto* p = arena_.Create<Process>();
    p->kind = ProcessKind::kAlways;
    p->id = next_id_++;
    p->home_region = Region::kActive;
    p->inst_prefix = set->members[i].clock_prefix;
    p->rng_seed = ctx_.DrawSeedForChild();
    p->coro = MakeAssumeClockCoroutine(*set, i, ctx_, arena_).Release();
    ScheduleProcess(p, ctx_);
  }
}

}  // namespace delta
