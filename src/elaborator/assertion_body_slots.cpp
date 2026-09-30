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

}  // namespace delta
