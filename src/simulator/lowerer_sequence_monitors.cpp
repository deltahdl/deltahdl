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
#include "elaborator/procedural_concurrent_assertion.h"
#include "elaborator/property_instance.h"
#include "elaborator/rtlir.h"
#include "elaborator/sensitivity.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"
#include "simulator/assertion_read_names.h"
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

std::unordered_set<std::string_view> TriggeredDependencies(
    const SeqLinearBody& body, SimContext& ctx) {
  std::unordered_set<std::string_view> deps;
  ForEachBodyExpr(body, [&](const Expr* e) {
    std::string_view name = TriggeredSequenceName(e, ctx);
    if (!name.empty()) deps.insert(name);
  });
  return deps;
}

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

struct TriggeredInstance {
  const Expr* instance;
  const ModuleItem* owner;
};

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
  auto collect_connection = [&](const Expr* e) {
    if (e->property_actual != nullptr &&
        e->property_actual->kind == PropertyExprNode::Kind::kBoolean &&
        !e->property_actual->clock.empty() && seen.insert(e).second) {
      actuals.push_back(e);
      return;
    }
    collect(e);
  };
  for (const auto* seq : mod->sequence_decls) {
    ForEachBodyExpr(seq->seq_linear, collect);
  }
  for (const auto& proc : mod->processes) {
    ForEachStmtReadExpr(proc.body,
                        [&](const Expr* e) { ForEachSubExpr(e, collect); });
  }
  for (const RtlirModuleInst& child : mod->children) {
    for (const RtlirPortBinding& binding : child.port_bindings) {
      ForEachSubExpr(binding.connection, collect_connection);
    }
  }
  return actuals;
}

ModuleItem* ActualAsSequence(const Expr* holder, std::string_view name,
                             Arena& arena) {
  const PropertyExprNode* tree = holder->property_actual;
  ModuleItem* seq = nullptr;
  if (tree->sequence != nullptr) {
    seq = arena.Create<ModuleItem>(*tree->sequence);
  } else {
    seq = arena.Create<ModuleItem>();
    SeqCycleDelay none;
    none.min = 0;
    none.max = 0;
    seq->seq_linear.operands.push_back(tree->boolean);
    seq->seq_linear.delays.push_back(none);
    seq->seq_linear.match_items.emplace_back();
    seq->seq_linear.repetitions.emplace_back();
  }
  seq->kind = ModuleItemKind::kSequenceDecl;
  seq->loc = holder->range.start;
  seq->name = name;
  if (seq->seq_clock.empty()) seq->seq_clock = holder->property_actual->clock;
  return seq;
}

bool DependenciesMade(const ModuleItem* seq,
                      const std::unordered_set<std::string_view>& made,
                      SimContext& ctx) {
  for (std::string_view dep : TriggeredDependencies(seq->seq_linear, ctx)) {
    if (dep != seq->name && made.count(dep) == 0) return false;
  }
  return true;
}

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
    for (const auto& proc : mod->processes) {
      if (proc.is_concurrent_clocked) continue;
      std::vector<EventExpr> clock = ProcessInferredClock(proc, mod);
      if (clock.empty()) continue;
      ForEachStmtReadExpr(proc.body,
                          [&](const Expr* e) { VisitExpr(e, clock, 0); });
    }
  }

  const std::vector<EventExpr>* FirstClockOf(std::string_view name) const {
    auto it = by_name_.find(name);
    return it == by_name_.end() ? nullptr : &it->second.front().clock;
  }

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
  if (seq->seq_triggered_unread) DropMatchCalls(body);
  if (body.clock.empty() && context_clock != nullptr) {
    body.clock = *context_clock;
  }
  if (body.clock.empty()) return;
  if (NamesAnotherClock(body)) return;
  std::unordered_set<std::string> names;
  ForEachLinearSequenceExpr(
      body, [&names](const Expr* e) { CollectSampledOperandNames(e, names); });
  if (!names.empty()) {
    AssertionSampleScope scope;
    scope.inst_prefix = inst_prefix_;
    scope.names.assign(names.begin(), names.end());
    assertion_sample_scopes_.push_back(std::move(scope));
  }
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
  const std::vector<EventExpr> kDefaultClock = DefaultClockingEvent(mod);
  auto lower_named = [&](const ModuleItem* seq) {
    const std::vector<EventExpr>* clock = context.FirstClockOf(seq->name);
    if (clock == nullptr) clock = &kDefaultClock;
    LowerNamedSequenceMonitor(seq, clock, context.FurtherClocksOf(seq->name));
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
      for (const ModuleItem* seq : deferred) lower_named(seq);
      break;
    }
    waiting = std::move(deferred);
  }
}

void RegisterModuleSequenceDecls(const RtlirModule* mod, SimContext& ctx) {
  for (auto* prop_decl : mod->property_decls) {
    ctx.RegisterPropertyDecl(prop_decl->name, prop_decl);
  }
  for (auto* seq_decl : mod->sequence_decls) {
    ctx.RegisterSequenceDecl(seq_decl->name, seq_decl);

    std::string ep_name = std::string("__seq_") + std::string(seq_decl->name);
    if (!ctx.FindVariable(ep_name)) {
      auto* stored = ctx.GetArena().Create<std::string>(
          ctx.ActiveInstancePrefix() + ep_name);
      auto* ep_var = ctx.CreateVariable(*stored, 1);
      ep_var->is_event = true;
    }
  }
}

}  // namespace delta
