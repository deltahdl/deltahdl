#include "elaborator/global_clock_assertion_event.h"

#include <cstddef>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

bool IsGlobalClockLeadingEvent(const std::vector<EventExpr>& sensitivity) {
  if (sensitivity.size() != 1) return false;
  const Expr* signal = sensitivity.front().signal;
  return signal != nullptr && signal->kind == ExprKind::kSystemCall &&
         signal->callee == "$global_clock";
}

bool SubstituteGlobalClockLeadingEvent(
    std::vector<EventExpr>& sensitivity,
    const std::vector<EventExpr>& global_event) {
  if (global_event.empty()) return false;
  if (!IsGlobalClockLeadingEvent(sensitivity)) return false;
  Expr* gate = sensitivity.front().iff_condition;
  sensitivity = global_event;
  for (auto& ev : sensitivity) {
    if (ev.iff_condition == nullptr) ev.iff_condition = gate;
  }
  return true;
}

namespace {

struct CloneOnWriteStmt {
  const Stmt* original;
  Stmt* current;
  Arena& arena;

  Stmt* Mutable() {
    if (current == original) current = arena.Create<Stmt>(*original);
    return current;
  }
};

void SubstituteGlobalClockInSubStmts(
    CloneOnWriteStmt& owner, const std::vector<EventExpr>& global_event) {
  std::vector<Stmt*> rewritten;
  bool any_rewritten = false;
  ForEachChildStmt(owner.original, [&](Stmt* const& sub) {
    Stmt* result =
        SubstituteGlobalClockEventControls(sub, global_event, owner.arena);
    if (result != sub) any_rewritten = true;
    rewritten.push_back(result);
  });
  if (!any_rewritten) return;
  size_t next = 0;
  ForEachChildStmt(owner.Mutable(),
                   [&](Stmt*& slot) { slot = rewritten[next++]; });
}

std::string_view InstancePathBelowTop(std::string_view inst_path) {
  size_t dot = inst_path.find('.');
  if (dot == std::string_view::npos) return {};
  return inst_path.substr(dot + 1);
}

Expr* MakeIdentifier(std::string_view text, const Expr* at, Arena& arena) {
  auto* id = arena.Create<Expr>();
  id->kind = ExprKind::kIdentifier;
  id->text = std::string_view(arena.AllocString(text.data(), text.size()),
                              text.size());
  id->range = at->range;
  return id;
}

Expr* MakeMemberAccess(Expr* base, std::string_view member, const Expr* at,
                       Arena& arena) {
  auto* acc = arena.Create<Expr>();
  acc->kind = ExprKind::kMemberAccess;
  acc->lhs = base;
  acc->rhs = MakeIdentifier(member, at, arena);
  acc->range = base->range;
  return acc;
}

constexpr std::string_view kRootScope = "$root";

Expr* RootQualifySignal(const Expr* signal, Arena& arena) {
  Expr* id = MakeIdentifier(signal->text, signal, arena);
  id->scope_prefix = kRootScope;
  return id;
}

Expr* QualifySignal(Expr* signal, std::string_view prefix, Arena& arena) {
  Expr* base = nullptr;
  size_t pos = 0;
  while (pos < prefix.size()) {
    size_t dot = prefix.find('.', pos);
    size_t end = dot == std::string_view::npos ? prefix.size() : dot;
    std::string_view component = prefix.substr(pos, end - pos);
    base = base == nullptr ? MakeIdentifier(component, signal, arena)
                           : MakeMemberAccess(base, component, signal, arena);
    pos = end + 1;
  }
  if (base == nullptr) return signal;
  return MakeMemberAccess(base, signal->text, signal, arena);
}

}  // namespace

const std::vector<EventExpr>* EffectiveGlobalClockingEvent(
    const std::vector<EventExpr>* declared_events,
    std::string_view declaring_inst_path,
    std::string_view referencing_inst_path, Arena& arena) {
  if (declared_events == nullptr) return nullptr;
  std::string_view declaring = InstancePathBelowTop(declaring_inst_path);
  std::string_view referencing = InstancePathBelowTop(referencing_inst_path);
  if (declaring == referencing) return declared_events;
  auto* qualified = arena.Create<std::vector<EventExpr>>(*declared_events);
  for (auto& ev : *qualified) {
    if (ev.signal == nullptr) continue;
    if (ev.signal->kind != ExprKind::kIdentifier) continue;
    ev.signal = declaring.empty() ? RootQualifySignal(ev.signal, arena)
                                  : QualifySignal(ev.signal, declaring, arena);
  }
  return qualified;
}

static void SubstituteGlobalClockInAssertionInstance(
    CloneOnWriteStmt& owner, const std::vector<EventExpr>& global_event) {
  const PropertyExprNode* root = owner.original->assert_property;
  if (root == nullptr) return;
  if (root->boolean != nullptr) {
    Expr* call = SubstituteGlobalClockInInstanceActuals(
        root->boolean, global_event, owner.arena);
    if (call == root->boolean) return;
    auto* copy = owner.arena.Create<PropertyExprNode>(*root);
    copy->boolean = call;
    Stmt* stmt = owner.Mutable();
    if (stmt->assert_instance == root->boolean) stmt->assert_instance = call;
    stmt->assert_property = copy;
    return;
  }
  if (root->sequence == nullptr ||
      root->sequence->seq_linear.operands.size() != 1) {
    return;
  }
  Expr* operand = root->sequence->seq_linear.operands.front();
  Expr* call = SubstituteGlobalClockInInstanceActuals(operand, global_event,
                                                      owner.arena);
  if (call == operand) return;
  auto* copy = owner.arena.Create<PropertyExprNode>(*root);
  copy->sequence = owner.arena.Create<ModuleItem>(*root->sequence);
  copy->sequence->seq_linear.operands.front() = call;
  owner.Mutable()->assert_property = copy;
}

Stmt* SubstituteGlobalClockEventControls(
    Stmt* stmt, const std::vector<EventExpr>& global_event, Arena& arena) {
  if (stmt == nullptr || global_event.empty()) return stmt;
  CloneOnWriteStmt owner{stmt, stmt, arena};
  if (IsGlobalClockLeadingEvent(stmt->events)) {
    SubstituteGlobalClockLeadingEvent(owner.Mutable()->events, global_event);
  }
  if (IsGlobalClockLeadingEvent(stmt->assert_clock)) {
    SubstituteGlobalClockLeadingEvent(owner.Mutable()->assert_clock,
                                      global_event);
  }
  SubstituteGlobalClockInAssertionInstance(owner, global_event);
  SubstituteGlobalClockInSubStmts(owner, global_event);
  return owner.current;
}

namespace {

bool ChainNamesGlobalClock(const SeqLinearBody& body) {
  for (const auto& clock : body.clocks) {
    if (IsGlobalClockLeadingEvent(clock)) return true;
  }
  for (const auto* chains :
       {&body.intersects, &body.conjuncts, &body.alternatives}) {
    for (const SeqLinearBody& chain : *chains) {
      if (ChainNamesGlobalClock(chain)) return true;
    }
  }
  return false;
}

bool TreeNamesGlobalClock(const PropertyExprNode* node) {
  if (node == nullptr) return false;
  if (IsGlobalClockLeadingEvent(node->clock)) return true;
  if (node->sequence != nullptr &&
      (IsGlobalClockLeadingEvent(node->sequence->seq_clock) ||
       ChainNamesGlobalClock(node->sequence->seq_linear))) {
    return true;
  }
  for (const PropertyExprNode* operand : node->operands) {
    if (TreeNamesGlobalClock(operand)) return true;
  }
  return false;
}

void SubstituteInChain(SeqLinearBody& body,
                       const std::vector<EventExpr>& global_event) {
  for (auto& clock : body.clocks) {
    SubstituteGlobalClockLeadingEvent(clock, global_event);
  }
  for (auto* chains : {&body.intersects, &body.conjuncts, &body.alternatives}) {
    for (SeqLinearBody& chain : *chains) SubstituteInChain(chain, global_event);
  }
}

PropertyExprNode* SubstitutedTree(const PropertyExprNode* node,
                                  const std::vector<EventExpr>& global_event,
                                  Arena& arena) {
  auto* copy = arena.Create<PropertyExprNode>(*node);
  SubstituteGlobalClockLeadingEvent(copy->clock, global_event);
  if (node->sequence != nullptr) {
    copy->sequence = arena.Create<ModuleItem>(*node->sequence);
    SubstituteGlobalClockLeadingEvent(copy->sequence->seq_clock, global_event);
    SubstituteInChain(copy->sequence->seq_linear, global_event);
  }
  for (PropertyExprNode*& operand : copy->operands) {
    operand = SubstitutedTree(operand, global_event, arena);
  }
  return copy;
}

}  // namespace

Expr* SubstituteGlobalClockInActual(Expr* actual,
                                    const std::vector<EventExpr>& global_event,
                                    Arena& arena) {
  if (actual == nullptr || global_event.empty() ||
      !TreeNamesGlobalClock(actual->property_actual)) {
    return actual;
  }
  auto* copy = arena.Create<Expr>(*actual);
  copy->property_actual =
      SubstitutedTree(actual->property_actual, global_event, arena);
  return copy;
}

Expr* SubstituteGlobalClockInInstanceActuals(
    Expr* call, const std::vector<EventExpr>& global_event, Arena& arena) {
  if (call == nullptr || call->kind != ExprKind::kCall) return call;
  std::vector<Expr*> args = call->args;
  bool rewritten = false;
  for (Expr*& arg : args) {
    Expr* substituted = SubstituteGlobalClockInActual(arg, global_event, arena);
    rewritten = rewritten || substituted != arg;
    arg = substituted;
  }
  if (!rewritten) return call;
  auto* copy = arena.Create<Expr>(*call);
  copy->args = std::move(args);
  return copy;
}

}  // namespace delta
