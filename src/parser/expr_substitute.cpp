#include "parser/expr_substitute.h"

#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

namespace delta {

Expr* SubstituteFormals(const Expr* e, const ActualsByFormal& actuals,
                        Arena& arena) {
  if (e == nullptr) return nullptr;
  if (e->kind == ExprKind::kIdentifier) {
    auto it = actuals.find(e->text);
    if (it != actuals.end()) return it->second;
  }
  auto* copy = arena.Create<Expr>(*e);
  copy->lhs = SubstituteFormals(e->lhs, actuals, arena);
  copy->rhs = SubstituteFormals(e->rhs, actuals, arena);
  copy->condition = SubstituteFormals(e->condition, actuals, arena);
  copy->true_expr = SubstituteFormals(e->true_expr, actuals, arena);
  copy->false_expr = SubstituteFormals(e->false_expr, actuals, arena);
  copy->base = SubstituteFormals(e->base, actuals, arena);
  copy->index = SubstituteFormals(e->index, actuals, arena);
  copy->index_end = SubstituteFormals(e->index_end, actuals, arena);
  copy->with_expr = SubstituteFormals(e->with_expr, actuals, arena);
  copy->repeat_count = SubstituteFormals(e->repeat_count, actuals, arena);
  for (auto& sub : copy->elements) sub = SubstituteFormals(sub, actuals, arena);
  for (auto& sub : copy->args) sub = SubstituteFormals(sub, actuals, arena);
  return copy;
}

ActualsByFormal BindActuals(const std::vector<std::string_view>& formals,
                            const Expr* instance) {
  ActualsByFormal actuals;
  if (instance->kind != ExprKind::kCall) return actuals;
  size_t named = instance->arg_names.size();
  size_t positional = instance->args.size() - named;
  for (size_t i = 0; i < positional && i < formals.size(); ++i) {
    actuals[formals[i]] = instance->args[i];
  }
  for (size_t i = 0; i < named; ++i) {
    actuals[instance->arg_names[i]] = instance->args[positional + i];
  }
  return actuals;
}

ActualsByFormal BindActualsWithDefaults(
    const std::vector<std::string_view>& formals,
    const std::vector<Expr*>& defaults, const Expr* instance) {
  ActualsByFormal actuals = BindActuals(formals, instance);
  for (size_t i = 0; i < formals.size() && i < defaults.size(); ++i) {
    if (defaults[i] == nullptr) continue;
    auto it = actuals.find(formals[i]);
    if (it == actuals.end() || it->second == nullptr) {
      actuals[formals[i]] = defaults[i];
    }
  }
  return actuals;
}

namespace {

bool IsEdgeEvent(const Expr* e) {
  return e->kind == ExprKind::kUnary &&
         (e->op == TokenKind::kKwPosedge || e->op == TokenKind::kKwNegedge ||
          e->op == TokenKind::kKwEdge);
}

bool IsJoint(const Expr* e, TokenKind op) {
  return e->kind == ExprKind::kBinary && e->op == op;
}

// §9.4.2: a guard holding where `own` and `other` both hold, the one alone
// where the other is null.
Expr* ConjoinGuards(Expr* own, Expr* other, Arena& arena) {
  if (own == nullptr) return other;
  if (other == nullptr) return own;
  auto* both = arena.Create<Expr>();
  both->kind = ExprKind::kBinary;
  both->op = TokenKind::kAmpAmp;
  both->lhs = own;
  both->rhs = other;
  both->range = own->range;
  return both;
}

void CollectEvents(Expr* e, std::vector<EventExpr>& out) {
  if (IsJoint(e, TokenKind::kKwOr)) {
    CollectEvents(e->lhs, out);
    CollectEvents(e->rhs, out);
    return;
  }
  EventExpr ev;
  if (IsJoint(e, TokenKind::kKwIff)) {
    ev.iff_condition = e->rhs;
    e = e->lhs;
  }
  ev.signal = e;
  if (IsEdgeEvent(e)) {
    ev.edge = e->op == TokenKind::kKwPosedge   ? Edge::kPosedge
              : e->op == TokenKind::kKwNegedge ? Edge::kNegedge
                                               : Edge::kEdge;
    ev.signal = e->lhs;
  }
  out.push_back(ev);
}

}  // namespace

bool IsEventActual(const Expr* actual) {
  return actual != nullptr &&
         (IsEdgeEvent(actual) || IsJoint(actual, TokenKind::kKwIff) ||
          IsJoint(actual, TokenKind::kKwOr));
}

std::vector<EventExpr> EventsOfActual(Expr* actual) {
  std::vector<EventExpr> events;
  CollectEvents(actual, events);
  return events;
}

void AppendActualEvents(const EventExpr& ev, Expr* actual, Arena& arena,
                        std::vector<EventExpr>& out) {
  for (const EventExpr& event : EventsOfActual(actual)) {
    EventExpr copy = ev;
    copy.edge = event.edge;
    copy.signal = event.signal;
    copy.iff_condition =
        ConjoinGuards(ev.iff_condition, event.iff_condition, arena);
    out.push_back(copy);
  }
}

std::string InstanceDeclName(const Expr* instance) {
  if (instance == nullptr) return {};
  if (instance->kind == ExprKind::kIdentifier) {
    return std::string(instance->text);
  }
  const Expr* path = instance;
  if (instance->kind == ExprKind::kCall) {
    if (!instance->callee.empty()) return std::string(instance->callee);
    path = instance->lhs;
  }
  if (path == nullptr || path->kind != ExprKind::kMemberAccess ||
      path->lhs == nullptr || path->rhs == nullptr ||
      path->lhs->kind != ExprKind::kIdentifier ||
      path->rhs->kind != ExprKind::kIdentifier) {
    return {};
  }
  std::string_view joint = path->is_scope_resolution ? "::" : ".";
  return std::string(path->lhs->text) + std::string(joint) +
         std::string(path->rhs->text);
}

bool SamePath(const Expr* a, const Expr* b) {
  if (a == nullptr || b == nullptr || a->kind != b->kind) return false;
  if (a->kind == ExprKind::kMemberAccess) {
    return a->is_scope_resolution == b->is_scope_resolution &&
           SamePath(a->lhs, b->lhs) && SamePath(a->rhs, b->rhs);
  }
  if (a->kind == ExprKind::kSelect) {
    return a->index_end == nullptr && b->index_end == nullptr &&
           SamePath(a->base, b->base) && SamePath(a->index, b->index);
  }
  if (a->kind == ExprKind::kIntegerLiteral) return a->int_val == b->int_val;
  return a->text == b->text && a->scope_prefix == b->scope_prefix;
}

}  // namespace delta
