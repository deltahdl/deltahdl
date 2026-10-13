#include <algorithm>
#include <cstddef>
#include <map>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"
#include "simulator/assertion_read_names.h"
#include "simulator/awaiters_event_control.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
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
// on, in the scope `clock_prefix` names; the condition it requires at each
// tick of that clock; and, for a nonoverlapped implication, the antecedent
// whose truth at one tick requires `next` at the following one.
struct AssumeSetMember {
  std::string clock_prefix;
  std::vector<EventExpr> clock;
  Expr* now = nullptr;
  Expr* antecedent = nullptr;
  Expr* next = nullptr;
  bool fired = false;
  bool pending = false;
};

// The assume set of a checker instance: `args` names the active free
// variables a solution attempt draws, `scope` is the process whose scope and
// random stream it draws them in, and `solves` holds the scope randomize call
// made for each set of conditions an attempt has been held to.
struct AssumeSet {
  std::vector<AssumeSetMember> members;
  std::vector<Expr*> args;
  Process* scope = nullptr;
  bool scheduled = false;
  std::map<std::vector<bool>, Expr*> solves;
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

// The scope randomize call an attempt makes over the conditions the members
// that ticked require: each one's condition, and the consequent each one
// owes from an antecedent that held at its previous tick.
Expr* SolveFor(AssumeSet& set, Arena& arena) {
  std::vector<bool> key;
  for (const AssumeSetMember& m : set.members) {
    key.push_back(m.fired && m.now != nullptr);
    key.push_back(m.fired && m.pending);
  }
  Expr*& solve = set.solves[key];
  if (solve != nullptr) return solve;
  auto* constraints = arena.Create<ClassMember>();
  for (size_t i = 0; i < set.members.size(); ++i) {
    if (key[2 * i]) {
      constraints->constraint_exprs.push_back(set.members[i].now);
    }
    if (key[(2 * i) + 1]) {
      constraints->constraint_exprs.push_back(set.members[i].next);
    }
  }
  solve = RandomizeCall(set.args, constraints, arena);
  return solve;
}

// §17.7.2: a solution attempt, made before the Observed region, reads every
// other variable at its sampled value and each active free variable at its
// current one, which the sampling store answers for it.
void AttemptSolution(AssumeSet& set, SimContext& ctx, Arena& arena) {
  Process* saved = ctx.CurrentProcess();
  ctx.SetCurrentProcess(set.scope);
  ctx.AssertionSamples().SetEvaluatingProperty(true);
  Logic4Vec drawn;
  TryEvalScopeRandomizeCall(SolveFor(set, arena), ctx, arena, drawn);
  for (AssumeSetMember& m : set.members) {
    if (m.fired && m.antecedent != nullptr) {
      m.pending = EvalExpr(m.antecedent, ctx, arena).IsTruthy();
    }
    m.fired = false;
  }
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

// §17.7.2: the assumption the process `proc` evaluates, lowered under
// `prefix`, as a member of an assume set: a boolean, required at each tick,
// or an implication of booleans, the overlapping one requiring its
// consequent where its antecedent holds at the same tick and the
// nonoverlapped one at the tick after. False for any other process.
bool MakeMember(const RtlirProcess& proc, const std::string& prefix,
                Arena& arena, AssumeSetMember& out) {
  const Stmt* body = proc.body;
  if (!proc.is_concurrent_clocked || body->kind != StmtKind::kAssumeImmediate) {
    return false;
  }
  out.clock_prefix = prefix;
  out.clock = proc.sensitivity;
  const PropertyExprNode* node = body->assert_property;
  if (node == nullptr) {
    out.now = body->assert_expr;
    return body->assert_sequence == nullptr && !body->assert_negated;
  }
  if (node->kind != PropertyExprNode::Kind::kImplication ||
      node->operands[0]->kind != PropertyExprNode::Kind::kBoolean) {
    return false;
  }
  const SeqLinearBody& seq = node->sequence->seq_linear;
  if (seq.operands.size() != 1 || seq.delays[0].max != 0) return false;
  Expr* consequent = node->operands[0]->boolean;
  if (node->strong) {
    out.antecedent = seq.operands[0];
    out.next = consequent;
    return true;
  }
  auto* implies = arena.Create<Expr>();
  implies->kind = ExprKind::kBinary;
  implies->op = TokenKind::kArrow;
  implies->lhs = seq.operands[0];
  implies->rhs = consequent;
  out.now = implies;
  return true;
}

std::unordered_set<std::string> ReadNames(const AssumeSetMember& m) {
  std::unordered_set<std::string> names;
  CollectSampledOperandNames(m.now, names);
  CollectSampledOperandNames(m.antecedent, names);
  CollectSampledOperandNames(m.next, names);
  return names;
}

bool ReadsAny(const AssumeSetMember& m,
              const std::unordered_set<std::string>& names) {
  return std::ranges::any_of(
      ReadNames(m), [&](const std::string& n) { return names.count(n) != 0; });
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

// §17.7.2: the assumptions of the checker `mod`, lowered under `prefix`, and
// those of its child checkers, each in `mod`'s terms, a child's formals
// replaced by its actuals; of them, one that reads a formal the instance
// `self` binds to a const cast or an automatic value is left out.
void CollectAssumptions(const RtlirModule* mod, const std::string& prefix,
                        const RtlirModuleInst& self, Arena& arena,
                        std::vector<AssumeSetMember>& out) {
  for (const RtlirProcess& proc : mod->processes) {
    AssumeSetMember m;
    if (MakeMember(proc, prefix, arena, m)) out.push_back(std::move(m));
  }
  // §17.2: a checker instantiates no other kind of definition.
  for (const RtlirModuleInst& child : mod->children) {
    ActualsByFormal actuals;
    for (const RtlirPortBinding& binding : child.port_bindings) {
      actuals[binding.port_name] = binding.connection;
    }
    std::vector<AssumeSetMember> inner;
    CollectAssumptions(child.resolved,
                       prefix + std::string(child.inst_name) + ".", child,
                       arena, inner);
    for (AssumeSetMember& m : inner) {
      m.now = SubstituteFormals(m.now, actuals, arena);
      m.antecedent = SubstituteFormals(m.antecedent, actuals, arena);
      m.next = SubstituteFormals(m.next, actuals, arena);
      out.push_back(std::move(m));
    }
  }
  const std::unordered_set<std::string> kBarred = BarredFormals(self);
  std::erase_if(out,
                [&](const AssumeSetMember& m) { return ReadsAny(m, kBarred); });
}

}  // namespace

// §17.7.2: every free variable of a checker instance whose declaration
// writes no initializer starts at an unconstrained random value, drawn from
// the instance's initialization stream. Its active free variables are then
// assigned, at each clock event of its assume set, values satisfying the
// assumptions of the set that ticked, found by §18.12's scope randomize over
// them with the conditions those assumptions require at that tick as its
// constraints; the other variables the conditions read stand at their
// sampled values. The set holds the instance's assumptions and its child
// checkers' that read one of its active free variables; where it holds none,
// the attempt is made, unconstrained, at every time step. An active free
// variable is read at its current value, which §17.7.2 makes its sampled
// value, so it is kept out of the sampling store.
void Lowerer::LowerFreeVariableSolver(const RtlirModule* mod) {
  if (!mod->random_initial_variables.empty()) {
    std::vector<Expr*> initial;
    for (std::string_view name : mod->random_initial_variables) {
      initial.push_back(NameExpr(name, arena_));
    }
    Logic4Vec drawn;
    TryEvalScopeRandomizeCall(RandomizeCall(initial, nullptr, arena_), ctx_,
                              arena_, drawn);
  }
  if (mod->free_variables.empty()) return;
  std::vector<AssumeSetMember> candidates;
  CollectAssumptions(mod, inst_prefix_, *lowering_inst_, arena_, candidates);
  auto* set = arena_.Create<AssumeSet>();
  std::unordered_set<std::string> active;
  for (std::string_view name : mod->free_variables) {
    active.emplace(name);
    set->args.push_back(NameExpr(name, arena_));
    ctx_.AssertionSamples().ExcludeFromSampling(ctx_.FindVariable(name));
  }
  for (AssumeSetMember& m : candidates) {
    if (ReadsAny(m, active)) set->members.push_back(std::move(m));
  }
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
