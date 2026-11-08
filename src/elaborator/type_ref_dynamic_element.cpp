#include "elaborator/type_ref_dynamic_element.h"

#include <algorithm>
#include <functional>
#include <initializer_list>
#include <optional>
#include <utility>

#include "common/source_loc.h"
#include "elaborator/expression_self_type.h"
#include "elaborator/unpacked_array_type.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

bool IsDynamicObject(const Expr* base, const ExprTypeScope& scope) {
  std::optional<DeclaredValue> value = ExprValue(base, scope);
  if (value && value->unpacked_dims != 0)
    return value->outermost != UnpackedKind::kFixed;
  std::optional<UnpackedArrayType> array = ExprSelfArrayType(base, scope);
  if (!array) return false;
  UnpackedArrayType whole = WithTypedefDims(
      array->element, std::move(array->dims), *scope.array_tables);
  return !whole.dims.empty() &&
         UnpackedDimKind(whole.dims.front(), *scope.array_tables) !=
             UnpackedKind::kFixed;
}

}  // namespace

bool SelectsDynamicElement(const Expr* e, const ExprTypeScope& scope) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kSelect && e->base != nullptr &&
      IsDynamicObject(e->base, scope)) {
    return true;
  }
  const Expr* const kChildren[] = {e->lhs,       e->rhs,        e->base,
                                   e->index,     e->index_end,  e->condition,
                                   e->true_expr, e->false_expr, e->with_expr};
  auto selects = [&](const Expr* child) {
    return SelectsDynamicElement(child, scope);
  };
  return std::ranges::any_of(kChildren, selects) ||
         std::ranges::any_of(e->elements, selects) ||
         std::ranges::any_of(e->args, selects);
}

void ForEachTypeRef(const Expr* e,
                    const std::function<void(const Expr*)>& on_ref) {
  if (e == nullptr) return;
  if (e->kind == ExprKind::kTypeRef) on_ref(e);
  const Expr* const kChildren[] = {e->lhs,       e->rhs,        e->base,
                                   e->index,     e->index_end,  e->condition,
                                   e->true_expr, e->false_expr, e->with_expr};
  for (const Expr* child : kChildren) ForEachTypeRef(child, on_ref);
  for (const Expr* elem : e->elements) ForEachTypeRef(elem, on_ref);
  for (const Expr* arg : e->args) ForEachTypeRef(arg, on_ref);
}

void ForEachTypeRefOfStmt(const Stmt* s,
                          const std::function<void(const Expr*)>& on_ref) {
  for (const Expr* e : {s->lhs, s->rhs, s->expr, s->condition, s->assert_expr,
                        s->for_cond, s->var_init}) {
    ForEachTypeRef(e, on_ref);
  }
  for (const CaseItem& item : s->case_items) {
    for (const Expr* pattern : item.patterns) ForEachTypeRef(pattern, on_ref);
  }
}

void ForEachItemExprTypeRef(
    const ModuleItem* item,
    const std::function<void(const Expr*, SourceLoc)>& on_ref) {
  auto in_expr = [&](const Expr* e) {
    ForEachTypeRef(
        e, [&](const Expr* ref) { on_ref(ref->lhs, ref->range.start); });
  };
  if (item->kind == ModuleItemKind::kContAssign) in_expr(item->assign_rhs);
  if (item->kind == ModuleItemKind::kParamDecl) in_expr(item->init_expr);
  if (item->kind != ModuleItemKind::kNetDecl &&
      item->kind != ModuleItemKind::kVarDecl) {
    return;
  }
  in_expr(item->data_type.packed_dim_left);
  in_expr(item->data_type.packed_dim_right);
  for (const auto& [left, right] : item->data_type.extra_packed_dims) {
    in_expr(left);
    in_expr(right);
  }
  for (const Expr* dim : item->unpacked_dims) in_expr(dim);
}

}  // namespace delta
