#include "elaborator/assertion_body_slots.h"

#include <string_view>
#include <unordered_set>

#include "common/arena.h"
#include "common/source_loc.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

Expr* MemberOf(std::string_view base, std::string_view member, SourceLoc loc,
               Arena& arena) {
  auto* lhs = arena.Create<Expr>();
  lhs->kind = ExprKind::kIdentifier;
  lhs->text = base;
  lhs->range.start = loc;
  auto* rhs = arena.Create<Expr>();
  rhs->kind = ExprKind::kIdentifier;
  rhs->text = member;
  rhs->range.start = loc;
  auto* access = arena.Create<Expr>();
  access->kind = ExprKind::kMemberAccess;
  access->lhs = lhs;
  access->rhs = rhs;
  access->range.start = loc;
  return access;
}

void CollectBodyLocals(const SeqLinearBody& body,
                       std::unordered_set<std::string_view>& out) {
  for (const SeqLocalDecl& local : body.locals) out.insert(local.name);
  for (const SeqLinearBody& inner : body.intersects) {
    CollectBodyLocals(inner, out);
  }
  for (const SeqLinearBody& inner : body.conjuncts) {
    CollectBodyLocals(inner, out);
  }
  for (const SeqLinearBody& inner : body.alternatives) {
    CollectBodyLocals(inner, out);
  }
}

void CollectTreeLocals(const PropertyExprNode* node,
                       std::unordered_set<std::string_view>& out) {
  if (node->sequence != nullptr) {
    CollectBodyLocals(node->sequence->seq_linear, out);
  }
  for (const PropertyExprNode* operand : node->operands) {
    CollectTreeLocals(operand, out);
  }
}

std::unordered_set<std::string_view> AssertionBoundNames(
    const ModuleItem* item) {
  std::unordered_set<std::string_view> bound(item->prop_formals.begin(),
                                             item->prop_formals.end());
  bound.insert(item->prop_seq_assert_vars.begin(),
               item->prop_seq_assert_vars.end());
  for (const SeqLocalDecl& local : item->prop_locals) bound.insert(local.name);
  CollectBodyLocals(item->seq_linear, bound);
  if (item->prop_body_tree != nullptr) {
    CollectTreeLocals(item->prop_body_tree, bound);
  }
  return bound;
}

}  // namespace delta
