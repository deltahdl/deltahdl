#include "elaborator/elaborator_bind_params.h"

#include <algorithm>
#include <cstddef>
#include <functional>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// §23.11: whether the dotted name `e`, read from `mod`, passes through an
// instance a bind put there: its leading names are instances one below the
// other, and one of them was bound.
bool DottedNameCrossesBind(const Expr* e, const RtlirModule* mod) {
  std::vector<std::string_view> steps;
  const Expr* head = e;
  while (head->kind == ExprKind::kMemberAccess && !head->is_scope_resolution) {
    steps.push_back(head->rhs->text);
    head = head->lhs;
  }
  if (head->kind != ExprKind::kIdentifier) return false;
  steps.push_back(head->text);
  for (size_t i = steps.size(); i-- > 1 && mod != nullptr;) {
    auto child = std::ranges::find_if(mod->children, [&](const auto& c) {
      return c.simple_inst_name == steps[i];
    });
    if (child == mod->children.end()) return false;
    if (child->is_bound) return true;
    mod = child->resolved;
  }
  return false;
}

// §23.11: whether some dotted name within `e` crosses a bind (above).
bool ExprCrossesBind(const Expr* e, const RtlirModule* mod) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kMemberAccess) return DottedNameCrossesBind(e, mod);
  bool found = false;
  ForEachExprChild(e, [&](const Expr* child) {
    found = found || ExprCrossesBind(child, mod);
  });
  return found;
}

// The packed range a declaration in a module's body writes, the constant
// expressions there a hierarchical name can reach a bind instance's parameter
// from; a parameter's value is held to §6.20.2's rule against any hierarchical
// reference already.
std::vector<const Expr*> ItemConstantExprs(const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kVarDecl &&
      item->kind != ModuleItemKind::kNetDecl) {
    return {};
  }
  std::vector<const Expr*> exprs{item->data_type.packed_dim_left,
                                 item->data_type.packed_dim_right};
  for (const auto& [left, right] : item->data_type.extra_packed_dims) {
    exprs.push_back(left);
    exprs.push_back(right);
  }
  return exprs;
}

// §23.11: the packed ranges of the declaration `decl` gives module `mod` that
// reach a bind instance's parameter, each reported at its declaration.
void ReportBindParamsInModule(const ModuleDecl* decl, const RtlirModule* mod,
                              DiagEngine& diag) {
  for (const ModuleItem* item : decl->items) {
    auto exprs = ItemConstantExprs(item);
    if (std::ranges::none_of(
            exprs, [mod](const Expr* e) { return ExprCrossesBind(e, mod); })) {
      continue;
    }
    diag.Error(item->loc,
               "a parameter of an instance a bind made is reached by a "
               "hierarchical name where a constant expression is required",
               Subclause("23.11"));
  }
}

}  // namespace

void ReportBindParamsInConstants(
    const std::vector<RtlirModule*>& tops,
    const std::function<const ModuleDecl*(std::string_view)>& find_module,
    DiagEngine& diag) {
  std::vector<const RtlirModule*> pending(tops.begin(), tops.end());
  std::unordered_set<const RtlirModule*> seen;
  while (!pending.empty()) {
    const RtlirModule* mod = pending.back();
    pending.pop_back();
    if (mod == nullptr || !seen.insert(mod).second) continue;
    for (const auto& child : mod->children) pending.push_back(child.resolved);
    const ModuleDecl* decl = find_module(mod->name);
    if (decl != nullptr) ReportBindParamsInModule(decl, mod, diag);
  }
}

}  // namespace delta
