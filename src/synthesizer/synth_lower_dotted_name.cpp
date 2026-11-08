#include <string_view>

#include "parser/ast_expr.h"
#include "synthesizer/synth_lower.h"

namespace delta {

static std::string_view DottedNameFirstComponent(const Expr* e) {
  const Expr* n = e;
  while (n && n->kind == ExprKind::kMemberAccess) n = n->lhs;
  if (n && n->kind == ExprKind::kIdentifier) return n->text;
  return {};
}

NonSynthRule SynthLower::DottedNameRule(const Expr* expr) const {
  if (expr->is_scope_resolution) {
    return {
        "a name with a scope resolution operator prefix has no lowering in "
        "the synthesizer",
        "23.7.1"};
  }
  if (signal_widths_.count(DottedNameFirstComponent(expr)) != 0) {
    return {"a member of a packed structure has no lowering in the synthesizer",
            "7.2.1"};
  }
  return {"a hierarchical name has no lowering in the synthesizer", "23.6"};
}

}  // namespace delta
