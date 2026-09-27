// §23.6: the flattened name a hierarchical reference is read by. A dotted
// name, `s.y` or `$root.t.s.y`, is spelled out from its parts, and the
// `$root.<top>.` a rooted one starts with is dropped, since the run keys what
// the top declares by its bare name and what an instance declares by its path
// below the top. Split out of eval_expr.cpp, which EvalMemberAccess still
// reads the name through, when that file reached the 950-line limit.

#include <string>
#include <string_view>

#include "parser/ast_expr.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/evaluation.h"

namespace delta {

static void BuildMemberName(const Expr* expr, std::string& out) {
  if (expr->kind == ExprKind::kIdentifier) {
    if (!expr->scope_prefix.empty()) {
      out += expr->scope_prefix;
      out += ".";
    }
    out += expr->text;
    return;
  }
  if (expr->kind == ExprKind::kMemberAccess) {
    BuildMemberName(expr->lhs, out);
    out += ".";
    BuildMemberName(expr->rhs, out);
  }
}

std::string StripRootPrefix(const std::string& name) {
  constexpr std::string_view kPrefix = "$root.";
  if (name.size() > kPrefix.size() &&
      std::string_view(name).substr(0, kPrefix.size()) == kPrefix) {
    auto rest = std::string_view(name).substr(kPrefix.size());
    auto dot = rest.find('.');
    if (dot != std::string_view::npos) return std::string(rest.substr(dot + 1));
    return std::string(rest);
  }
  return name;
}

std::string HierarchicalReferenceName(const Expr* expr) {
  std::string name;
  BuildMemberName(expr, name);
  return StripRootPrefix(name);
}

}  // namespace delta
