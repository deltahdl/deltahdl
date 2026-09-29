#include <format>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

void CollectIdentLeaves(const Expr* e, std::vector<const Expr*>& out) {
  if (!e) return;
  switch (e->kind) {
    case ExprKind::kIdentifier:
      if (!e->text.empty() && e->text.front() != '$') out.push_back(e);
      return;
    case ExprKind::kCall:
    case ExprKind::kSystemCall:
      for (auto* a : e->args) CollectIdentLeaves(a, out);
      return;
    case ExprKind::kMemberAccess:
      CollectIdentLeaves(e->lhs, out);
      return;
    case ExprKind::kTypeRef:
      return;
    default:
      break;
  }
  CollectIdentLeaves(e->lhs, out);
  CollectIdentLeaves(e->rhs, out);
  CollectIdentLeaves(e->base, out);
  CollectIdentLeaves(e->index, out);
  CollectIdentLeaves(e->index_end, out);
  CollectIdentLeaves(e->condition, out);
  CollectIdentLeaves(e->true_expr, out);
  CollectIdentLeaves(e->false_expr, out);
  CollectIdentLeaves(e->repeat_count, out);
  CollectIdentLeaves(e->with_expr, out);
  for (auto* a : e->args) CollectIdentLeaves(a, out);
  for (auto* el : e->elements) CollectIdentLeaves(el, out);
}

// Reports each identifier leaf of a default-value expression that is neither a
// previously declared argument nor visible in the subroutine's declaring scope.
template <typename InModuleScopeFn>
void CheckOneArgDefaultScope(
    const FunctionArg& arg,
    const std::unordered_set<std::string_view>& prior_args,
    const InModuleScopeFn& in_module_scope, DiagEngine& diag) {
  std::vector<const Expr*> idents;
  CollectIdentLeaves(arg.default_value, idents);
  for (const auto* e : idents) {
    auto name = e->text;
    if (name.empty()) continue;
    if (prior_args.count(name)) continue;
    if (in_module_scope(name)) continue;
    diag.Error(e->range.start,
               std::format("default value for '{}' references '{}' "
                           "which is not declared in the subroutine's "
                           "declaring scope",
                           arg.name, name),
               Subclause("13.5.3"));
  }
}

}  // namespace

void Elaborator::ValidateFunctionArgDefaultsScope(const ModuleItem* item) {
  if (!item) return;
  if (!item->is_ansi_ports) return;
  if (!item->method_class.empty()) return;
  auto in_module_scope = [this](std::string_view name) {
    return IsNameInModuleScope(name);
  };
  std::unordered_set<std::string_view> prior_args;
  for (const auto& arg : item->func_args) {
    if (arg.default_value) {
      CheckOneArgDefaultScope(arg, prior_args, in_module_scope, diag_);
    }
    if (!arg.name.empty()) prior_args.insert(arg.name);
  }
}

}  // namespace delta
