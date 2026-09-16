#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "parser/ast.h"
#include "simulator/expr_walk.h"
#include "simulator/lowerer.h"
#include "simulator/process.h"
#include "simulator/sequence_flatten.h"
#include "simulator/sequence_monitor.h"
#include "simulator/sim_context.h"

namespace delta {
namespace {

// §16.9.11 and §16.13.5: whether the expression applies `triggered` or
// `matched` to a named sequence, as `e1.triggered` or `e2(ready, proc1,
// proc2).matched`, and if so the sequence's name.
std::string_view TriggeredSequenceName(const Expr* e, SimContext& ctx) {
  if (e->kind != ExprKind::kMemberAccess || e->lhs == nullptr ||
      e->rhs == nullptr ||
      (e->rhs->text != "triggered" && e->rhs->text != "matched")) {
    return {};
  }
  std::string_view name;
  if (e->lhs->kind == ExprKind::kIdentifier) name = e->lhs->text;
  if (e->lhs->kind == ExprKind::kCall) name = e->lhs->callee;
  return ctx.FindSequenceDecl(name) != nullptr ? name : std::string_view{};
}

// Every expression a sequence body holds: its operands and match items, and
// those of its intersects, conjuncts and alternatives.
template <typename Fn>
void ForEachBodyExpr(const SeqLinearBody& body, const Fn& fn) {
  for (const Expr* operand : body.operands) ForEachSubExpr(operand, fn);
  for (const auto& items : body.match_items) {
    for (const SeqMatchAssign& item : items) ForEachSubExpr(item.rhs, fn);
  }
  for (const SeqLinearBody& inner : body.intersects) ForEachBodyExpr(inner, fn);
  for (const SeqLinearBody& inner : body.conjuncts) ForEachBodyExpr(inner, fn);
  for (const SeqLinearBody& inner : body.alternatives) {
    ForEachBodyExpr(inner, fn);
  }
}

// The names of the sequences a body applies `triggered` to, whose end points
// its monitor reads at the tick they are reached, so whose monitors run
// first at each tick.
std::unordered_set<std::string_view> TriggeredDependencies(
    const SeqLinearBody& body, SimContext& ctx) {
  std::unordered_set<std::string_view> deps;
  ForEachBodyExpr(body, [&](const Expr* e) {
    std::string_view name = TriggeredSequenceName(e, ctx);
    if (!name.empty()) deps.insert(name);
  });
  return deps;
}

// The instances with arguments the module applies `triggered` to, in its
// sequence bodies and its procedures, each once.
std::vector<const Expr*> TriggeredInstances(const RtlirModule* mod,
                                            SimContext& ctx) {
  std::vector<const Expr*> instances;
  std::unordered_set<const Expr*> seen;
  auto collect = [&](const Expr* e) {
    if (TriggeredSequenceName(e, ctx).empty()) return;
    if (e->lhs->kind != ExprKind::kCall || !seen.insert(e->lhs).second) return;
    instances.push_back(e->lhs);
  };
  for (const auto* seq : mod->sequence_decls) {
    ForEachBodyExpr(seq->seq_linear, collect);
  }
  for (const auto& proc : mod->processes) {
    ForEachStmtReadExpr(proc.body,
                        [&](const Expr* e) { ForEachSubExpr(e, collect); });
  }
  return instances;
}

// §16.13.6: the sequence actuals the module's bodies pass to instances,
// `e2_with_arg(@(posedge sysclk) $rose(a) ##1 b ##1 c)`, each carried by
// the identifier standing in the argument's place, in its sequence bodies
// and its procedures, each once. A method the instantiated body applies to
// the formal, `subseq.triggered`, reads the end point of the actual's own
// monitor.
std::vector<const Expr*> SequenceActuals(const RtlirModule* mod) {
  std::vector<const Expr*> actuals;
  std::unordered_set<const Expr*> seen;
  auto collect = [&](const Expr* e) {
    if (e->kind != ExprKind::kIdentifier || e->property_actual == nullptr ||
        e->property_actual->kind != PropertyExprNode::Kind::kSequence ||
        e->property_actual->sequence == nullptr || !seen.insert(e).second) {
      return;
    }
    actuals.push_back(e);
  };
  for (const auto* seq : mod->sequence_decls) {
    ForEachBodyExpr(seq->seq_linear, collect);
  }
  for (const auto& proc : mod->processes) {
    ForEachStmtReadExpr(proc.body,
                        [&](const Expr* e) { ForEachSubExpr(e, collect); });
  }
  return actuals;
}

// §16.13.6: the sequence_expr an actual carries as a declaration of its
// own, on the clock the actual opens with, `@(posedge sysclk)`, where it
// opens with one.
ModuleItem* ActualAsSequence(const Expr* holder, std::string_view name,
                             Arena& arena) {
  auto* seq = arena.Create<ModuleItem>(*holder->property_actual->sequence);
  seq->kind = ModuleItemKind::kSequenceDecl;
  seq->loc = holder->range.start;
  seq->name = name;
  if (seq->seq_clock.empty()) seq->seq_clock = holder->property_actual->clock;
  return seq;
}

// Whether every sequence the body applies `triggered` to, itself aside, has
// its monitor made.
bool DependenciesMade(const ModuleItem* seq,
                      const std::unordered_set<std::string_view>& made,
                      SimContext& ctx) {
  for (std::string_view dep : TriggeredDependencies(seq->seq_linear, ctx)) {
    if (dep != seq->name && made.count(dep) == 0) return false;
  }
  return true;
}

// §16.9.11: `e2(ready, proc1, proc2).triggered` is `e2_instantiated.triggered`
// for a sequence e2_instantiated whose body is the instance, so the instance
// is given a declaration of that shape, clockless, the flattening taking the
// clock from e2's own.
ModuleItem* InstanceAsSequence(const Expr* instance, std::string_view name,
                               Arena& arena) {
  auto* seq = arena.Create<ModuleItem>();
  seq->kind = ModuleItemKind::kSequenceDecl;
  seq->loc = instance->range.start;
  seq->name = name;
  seq->seq_linear.operands.push_back(const_cast<Expr*>(instance));
  seq->seq_linear.delays.emplace_back();
  seq->seq_linear.delays.back().min = 0;
  seq->seq_linear.delays.back().max = 0;
  seq->seq_linear.match_items.emplace_back();
  seq->seq_linear.repetitions.emplace_back();
  return seq;
}

}  // namespace

// §16.13.6/§9.4.4: spawn a monitor process for one named sequence whose
// clocked linear body the flattening reads, so its endpoint event fires on a
// match and `sequence.triggered` and `wait` observe it. §16.8: a sequence
// declared without a clock is matched through the sequences that
// instantiate it, which inherit it into their own bodies, unless an instance
// in it names the clock through an event formal (§16.8.1), which the
// flattening then answers as the sequence's own.
void Lowerer::LowerSequenceMonitor(const ModuleItem* seq,
                                   std::string_view ep_name) {
  LinearSequence body;
  if (!FlattenLinearSequence(seq, ctx_, arena_, body)) return;
  if (body.clock.empty()) return;
  // §16.13.1: a sequence whose operands name a clock other than its own is
  // matched where a property holds it, which tells the clocks apart; the
  // monitor, on the one clock, does not.
  if (NamesAnotherClock(body)) return;
  auto* p = arena_.Create<Process>();
  p->kind = ProcessKind::kAlways;
  p->id = next_id_++;
  p->home_region = Region::kActive;
  p->inst_prefix = inst_prefix_;
  p->rng_seed = ctx_.DrawSeedForChild();
  std::vector<EventExpr> clock = body.clock;
  p->coro = MakeSequenceMonitorCoroutine(std::move(body), std::move(clock),
                                         std::string(ep_name), ctx_, arena_)
                .Release();
  ScheduleProcess(p, ctx_);
}

// §16.9.11 and §16.13.6: the monitors of a module's sequences, the
// sequence actuals its bodies pass and the instances with arguments its
// bodies apply `triggered` to first, each under an endpoint of its own that
// the evaluator finds by the actual or the instance, and then the named
// sequences, a sequence reading another's `triggered` after the one it
// reads, so that at each tick the end point is fired before it is read; a
// cycle among them is broken in declaration order.
void Lowerer::LowerSequenceMonitors(const RtlirModule* mod) {
  for (const Expr* actual : SequenceActuals(mod)) {
    auto* name =
        arena_.Create<std::string>("actual@" + std::to_string(next_id_));
    auto* ep_name = arena_.Create<std::string>("__seq_" + *name);
    auto* ep_var = ctx_.CreateVariable(*ep_name, 1);
    ep_var->is_event = true;
    ctx_.RegisterSequenceInstanceEndpoint(actual, *ep_name);
    LowerSequenceMonitor(ActualAsSequence(actual, *name, arena_), *ep_name);
  }
  for (const Expr* instance : TriggeredInstances(mod, ctx_)) {
    auto* name = arena_.Create<std::string>(std::string(instance->callee) +
                                            "@" + std::to_string(next_id_));
    auto* ep_name = arena_.Create<std::string>("__seq_" + *name);
    auto* ep_var = ctx_.CreateVariable(*ep_name, 1);
    ep_var->is_event = true;
    ctx_.RegisterSequenceInstanceEndpoint(instance, *ep_name);
    LowerSequenceMonitor(InstanceAsSequence(instance, *name, arena_), *ep_name);
  }
  std::vector<const ModuleItem*> waiting(mod->sequence_decls.begin(),
                                         mod->sequence_decls.end());
  std::unordered_set<std::string_view> made;
  while (!waiting.empty()) {
    std::vector<const ModuleItem*> deferred;
    for (const ModuleItem* seq : waiting) {
      if (!DependenciesMade(seq, made, ctx_)) {
        deferred.push_back(seq);
        continue;
      }
      LowerSequenceMonitor(seq, "__seq_" + std::string(seq->name));
      made.insert(seq->name);
    }
    if (deferred.size() == waiting.size()) {
      // A cycle: the rest are made in declaration order.
      for (const ModuleItem* seq : deferred) {
        LowerSequenceMonitor(seq, "__seq_" + std::string(seq->name));
      }
      break;
    }
    waiting = std::move(deferred);
  }
}

}  // namespace delta
