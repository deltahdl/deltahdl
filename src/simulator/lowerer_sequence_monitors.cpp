#include <cstddef>
#include <memory>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"
#include "simulator/expr_walk.h"
#include "simulator/lowerer.h"
#include "simulator/lowerer_register.h"
#include "simulator/process.h"
#include "simulator/sequence_flatten.h"
#include "simulator/sequence_local_flow.h"
#include "simulator/sequence_monitor.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

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

// Whether the body of `decl` applies `triggered` or `matched` to its formal
// `formal`, as `a.triggered`.
bool AppliesMethodToFormal(const ModuleItem* decl, std::string_view formal) {
  bool applies = false;
  ForEachBodyExpr(decl->seq_linear, [&](const Expr* e) {
    if (e->kind == ExprKind::kMemberAccess && e->lhs != nullptr &&
        e->rhs != nullptr && e->lhs->kind == ExprKind::kIdentifier &&
        e->lhs->text == formal &&
        (e->rhs->text == "triggered" || e->rhs->text == "matched")) {
      applies = true;
    }
  });
  return applies;
}

// §16.9.11 with §16.8.1 (a): the instances with arguments bound as actuals of
// `instance` to formals of type sequence that the instantiated body applies
// `triggered` or `matched` to, which the method, once the formal is
// replaced, reads the end point of.
void SequenceFormalInstances(const Expr* instance, SimContext& ctx,
                             std::vector<const Expr*>& out) {
  if (instance->kind != ExprKind::kCall) return;
  const ModuleItem* decl = ctx.FindSequenceDecl(instance->callee);
  if (decl == nullptr) return;
  ActualsByFormal actuals = BindActualsWithDefaults(
      decl->prop_formals, decl->prop_formal_defaults, instance);
  for (size_t i = 0;
       i < decl->prop_formals.size() && i < decl->prop_formal_type_kw.size();
       ++i) {
    if (decl->prop_formal_type_kw[i] != TokenKind::kKwSequence) continue;
    auto it = actuals.find(decl->prop_formals[i]);
    if (it == actuals.end() || it->second == nullptr ||
        it->second->kind != ExprKind::kCall ||
        ctx.FindSequenceDecl(it->second->callee) == nullptr ||
        !AppliesMethodToFormal(decl, decl->prop_formals[i])) {
      continue;
    }
    out.push_back(it->second);
  }
}

// An instance with arguments `triggered` is applied to, and the sequence
// whose body applies it, null for a procedure.
struct TriggeredInstance {
  const Expr* instance;
  const ModuleItem* owner;
};

// The instances with arguments the module applies `triggered` to, in its
// sequence bodies and its procedures, directly or through a formal of type
// sequence, each once.
std::vector<TriggeredInstance> TriggeredInstances(const RtlirModule* mod,
                                                  SimContext& ctx) {
  std::vector<TriggeredInstance> instances;
  std::unordered_set<const Expr*> seen;
  const ModuleItem* owner = nullptr;
  auto collect = [&](const Expr* e) {
    std::vector<const Expr*> found;
    SequenceFormalInstances(e, ctx, found);
    if (!TriggeredSequenceName(e, ctx).empty() &&
        e->lhs->kind == ExprKind::kCall) {
      found.push_back(e->lhs);
    }
    for (const Expr* instance : found) {
      if (seen.insert(instance).second) instances.push_back({instance, owner});
    }
  };
  for (const auto* seq : mod->sequence_decls) {
    owner = seq;
    ForEachBodyExpr(seq->seq_linear, collect);
  }
  owner = nullptr;
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
// clock from e2's own. §16.10: a local of `owner` passed as an entire actual
// is declared in it too, so the instance's match assigns it and the end point
// hands the value on; its initialization is left out, the formal being
// assigned before it is read.
ModuleItem* InstanceAsSequence(const TriggeredInstance& triggered,
                               std::string_view name, Arena& arena) {
  const Expr* instance = triggered.instance;
  auto* seq = arena.Create<ModuleItem>();
  seq->kind = ModuleItemKind::kSequenceDecl;
  seq->loc = instance->range.start;
  seq->name = name;
  if (triggered.owner != nullptr) {
    for (SeqLocalDecl local : triggered.owner->seq_linear.locals) {
      if (!PassedAsWholeActual(instance, local.name)) continue;
      local.init = nullptr;
      seq->seq_linear.locals.push_back(local);
    }
  }
  seq->seq_linear.operands.push_back(const_cast<Expr*>(instance));
  seq->seq_linear.delays.emplace_back();
  seq->seq_linear.delays.back().min = 0;
  seq->seq_linear.delays.back().max = 0;
  seq->seq_linear.match_items.emplace_back();
  seq->seq_linear.repetitions.emplace_back();
  return seq;
}

// §16.9.11 with §16.13.5 and §16.16: the clock a sequence declared without
// one takes where `triggered` is applied to it, the clock of the context the
// method is read in, kept for each read of `e.triggered`, `e` as written in
// it, under the sequence's name, and for the instance of `e2(a).triggered`.
// The walk starts at each concurrent assertion on its leading clock and
// enters the sequences it instantiates, a clockless one on the clock flowing
// to it and a clocked one on its own; the first clock an instance is read on
// is kept.
// Whether two clocks are the same events, edge by edge over signals of the
// same spelling.
bool SameClock(const std::vector<EventExpr>& a,
               const std::vector<EventExpr>& b) {
  for (size_t i = 0; i < a.size() && i < b.size(); ++i) {
    if (a[i].edge != b[i].edge || !SamePath(a[i].signal, b[i].signal)) {
      return false;
    }
  }
  return a.size() == b.size();
}

struct NamedRead {
  const Expr* sequence;
  std::vector<EventExpr> clock;
};

class TriggeredContextClocks {
 public:
  TriggeredContextClocks(const RtlirModule* mod, SimContext& ctx) : ctx_(ctx) {
    for (const auto& proc : mod->processes) {
      const Stmt* stmt = proc.body;
      if (!proc.is_concurrent_clocked || stmt == nullptr) continue;
      const std::vector<EventExpr>& clock = stmt->assert_clock;
      VisitExpr(stmt->assert_expr, clock, 0);
      VisitSequence(stmt->assert_sequence, clock, 0);
      VisitTree(stmt->assert_property, clock, 0);
    }
  }

  // The clock of the first context reading `triggered` of the sequence
  // `name`, null where none reads it.
  const std::vector<EventExpr>* FirstClockOf(std::string_view name) const {
    auto it = by_name_.find(name);
    return it == by_name_.end() ? nullptr : &it->second.front().clock;
  }

  // The reads of the sequence `name` on clocks other than the first, grouped
  // by clock, each read by `name` as it stands in it.
  std::vector<ClockReads> FurtherClocksOf(std::string_view name) const {
    std::vector<ClockReads> further;
    auto it = by_name_.find(name);
    if (it == by_name_.end()) return further;
    const std::vector<EventExpr>& first = it->second.front().clock;
    for (const NamedRead& read : it->second) {
      if (SameClock(read.clock, first)) continue;
      ClockReads* group = nullptr;
      for (ClockReads& have : further) {
        if (SameClock(have.first, read.clock)) group = &have;
      }
      if (group == nullptr) {
        group = &further.emplace_back(read.clock, std::vector<const Expr*>{});
      }
      group->second.push_back(read.sequence);
    }
    return further;
  }
  const std::vector<EventExpr>* OfInstance(const Expr* instance) const {
    auto it = by_instance_.find(instance);
    return it == by_instance_.end() ? nullptr : &it->second;
  }

 private:
  static constexpr int kMaxDepth = 8;

  void VisitTree(const PropertyExprNode* node,
                 const std::vector<EventExpr>& clock, int depth) {
    if (node == nullptr) return;
    const std::vector<EventExpr>& own =
        node->clock.empty() ? clock : node->clock;
    VisitExpr(node->boolean, own, depth);
    VisitSequence(node->sequence, own, depth);
    for (const PropertyExprNode* operand : node->operands) {
      VisitTree(operand, own, depth);
    }
  }

  void VisitSequence(const ModuleItem* seq, const std::vector<EventExpr>& clock,
                     int depth) {
    if (seq == nullptr || depth >= kMaxDepth) return;
    const std::vector<EventExpr>& own =
        seq->seq_clock.empty() ? clock : seq->seq_clock;
    ForEachBodyExpr(seq->seq_linear,
                    [&](const Expr* e) { VisitOne(e, own, depth); });
  }

  void VisitExpr(const Expr* e, const std::vector<EventExpr>& clock,
                 int depth) {
    if (e == nullptr) return;
    ForEachSubExpr(e, [&](const Expr* sub) { VisitOne(sub, clock, depth); });
  }

  // One subexpression: an application of `triggered` records the clock for
  // the read or the instance it reads, and an instance, that one's operand
  // among them, enters the sequence.
  void VisitOne(const Expr* e, const std::vector<EventExpr>& clock, int depth) {
    std::string_view read = TriggeredSequenceName(e, ctx_);
    if (!read.empty() && e->lhs->kind == ExprKind::kCall) {
      by_instance_.emplace(e->lhs, clock);
    } else if (!read.empty()) {
      by_name_[read].push_back({e->lhs, clock});
    }
    std::string_view name;
    if (e->kind == ExprKind::kIdentifier) name = e->text;
    if (e->kind == ExprKind::kCall) name = e->callee;
    const ModuleItem* decl = ctx_.FindSequenceDecl(name);
    if (decl != nullptr) VisitSequence(decl, clock, depth + 1);
  }

  SimContext& ctx_;
  std::unordered_map<std::string_view, std::vector<NamedRead>> by_name_;
  std::unordered_map<const Expr*, std::vector<EventExpr>> by_instance_;
};

}  // namespace

// §16.13.6/§9.4.4: spawn a monitor process for one named sequence whose
// clocked linear body the flattening reads, so its endpoint event fires on a
// match and `sequence.triggered` and `wait` observe it. §16.8: a sequence
// declared without a clock is matched through the sequences that
// instantiate it, which inherit it into their own bodies, unless an instance
// in it names the clock through an event formal (§16.8.1), which the
// flattening then answers as the sequence's own. §16.9.11: where `triggered`
// is applied to it, it takes the clock of the context the method is read in,
// `context_clock`.
// §16.11: `body` without the subroutine calls its match items attach, in its
// nested operands and its intersect, and and or operands too.
static void DropMatchCalls(LinearSequence& body) {
  for (std::vector<SeqMatchAssign>& items : body.match_items) {
    std::erase_if(
        items, [](const SeqMatchAssign& item) { return item.call != nullptr; });
  }
  for (auto* list : {&body.intersects, &body.conjuncts, &body.alternatives}) {
    for (LinearSequence& inner : *list) DropMatchCalls(inner);
  }
  for (auto& entry : body.nested) {
    LinearSequence inner = *entry.second;
    DropMatchCalls(inner);
    entry.second = std::make_shared<const LinearSequence>(std::move(inner));
  }
}

void Lowerer::LowerSequenceMonitor(
    const ModuleItem* seq, std::string_view ep_name,
    const std::vector<EventExpr>* context_clock) {
  LinearSequence body;
  if (!FlattenLinearSequence(seq, ctx_, arena_, body)) return;
  // §16.11 with §16.13.6: a monitor no `triggered` or `matched` read asks for
  // is no evaluation the source instantiates, so the calls attached to the
  // sequence are left to the evaluations that do, run at their end points.
  if (seq->seq_triggered_unread) DropMatchCalls(body);
  if (body.clock.empty() && context_clock != nullptr) {
    body.clock = *context_clock;
  }
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

// §16.13.6 with §23.9: the event of an end point `ep_name` the monitor fires
// and `triggered` reads, declared in the instance being lowered.
void Lowerer::CreateEndPoint(std::string_view ep_name) {
  const auto* key =
      arena_.Create<std::string>(inst_prefix_ + std::string(ep_name));
  ctx_.CreateVariable(*key, 1)->is_event = true;
}

void Lowerer::LowerNamedSequenceMonitor(
    const ModuleItem* seq, const std::vector<EventExpr>* first_clock,
    const std::vector<ClockReads>& further) {
  LowerSequenceMonitor(seq, "__seq_" + std::string(seq->name), first_clock);
  if (!seq->seq_clock.empty()) return;
  for (const ClockReads& reads : further) {
    auto* ep_name = arena_.Create<std::string>(
        "__seq_" + std::string(seq->name) + "@" + std::to_string(next_id_));
    CreateEndPoint(*ep_name);
    LowerSequenceMonitor(seq, *ep_name, &reads.first);
    for (const Expr* read : reads.second) {
      ctx_.RegisterSequenceInstanceEndpoint(read, *ep_name);
    }
  }
}

// §16.9.11 and §16.13.6: the monitors of a module's sequences, the
// sequence actuals its bodies pass and the instances with arguments its
// bodies apply `triggered` to first, each under an endpoint of its own that
// the evaluator finds by the actual or the instance, and then the named
// sequences, a sequence reading another's `triggered` after the one it
// reads, so that at each tick the end point is fired before it is read; a
// cycle among them is broken in declaration order.
void Lowerer::LowerSequenceMonitors(const RtlirModule* mod) {
  TriggeredContextClocks context(mod, ctx_);
  for (const Expr* actual : SequenceActuals(mod)) {
    auto* name =
        arena_.Create<std::string>("actual@" + std::to_string(next_id_));
    auto* ep_name = arena_.Create<std::string>("__seq_" + *name);
    CreateEndPoint(*ep_name);
    ctx_.RegisterSequenceInstanceEndpoint(actual, *ep_name);
    LowerSequenceMonitor(ActualAsSequence(actual, *name, arena_), *ep_name,
                         nullptr);
  }
  for (const TriggeredInstance& triggered : TriggeredInstances(mod, ctx_)) {
    const Expr* instance = triggered.instance;
    auto* name = arena_.Create<std::string>(std::string(instance->callee) +
                                            "@" + std::to_string(next_id_));
    auto* ep_name = arena_.Create<std::string>("__seq_" + *name);
    CreateEndPoint(*ep_name);
    ctx_.RegisterSequenceInstanceEndpoint(instance, *ep_name);
    LowerSequenceMonitor(InstanceAsSequence(triggered, *name, arena_), *ep_name,
                         context.OfInstance(instance));
  }
  auto lower_named = [&](const ModuleItem* seq) {
    LowerNamedSequenceMonitor(seq, context.FirstClockOf(seq->name),
                              context.FurtherClocksOf(seq->name));
  };
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
      lower_named(seq);
      made.insert(seq->name);
    }
    if (deferred.size() == waiting.size()) {
      // A cycle: the rest are made in declaration order.
      for (const ModuleItem* seq : deferred) lower_named(seq);
      break;
    }
    waiting = std::move(deferred);
  }
}

// §16.8 and §16.12: each named property and sequence of the module under its
// name, and each sequence's end-point event, which `.triggered` reads.
void RegisterModuleSequenceDecls(const RtlirModule* mod, SimContext& ctx) {
  for (auto* prop_decl : mod->property_decls) {
    ctx.RegisterPropertyDecl(prop_decl->name, prop_decl);
  }
  for (auto* seq_decl : mod->sequence_decls) {
    ctx.RegisterSequenceDecl(seq_decl->name, seq_decl);

    std::string ep_name = std::string("__seq_") + std::string(seq_decl->name);
    if (!ctx.FindVariable(ep_name)) {
      // variables_ keys by string_view, so the key's backing string must
      // outlive the map; intern it in the arena. A local std::string would
      // dangle and make every later FindVariable("__seq_<name>") miss.
      // §23.9: the end point is declared in the instance being built, so
      // each instance of a module has one of its own.
      auto* stored = ctx.GetArena().Create<std::string>(
          ctx.ActiveInstancePrefix() + ep_name);
      auto* ep_var = ctx.CreateVariable(*stored, 1);
      ep_var->is_event = true;
    }
  }
}

}  // namespace delta
