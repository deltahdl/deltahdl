#include "simulator/eval_class_scope_types.h"

#include <cstddef>
#include <cstdint>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/class_specialization.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

static const Expr* SpecializationElement(const Expr& base, size_t pos,
                                         std::string_view pname) {
  for (size_t j = 0; j < base.elements.size(); ++j) {
    if (j < base.arg_names.size() && base.arg_names[j] == pname)
      return base.elements[j];
  }
  if (pos >= base.elements.size()) return nullptr;
  bool named = pos < base.arg_names.size() && !base.arg_names[pos].empty();
  return named ? nullptr : base.elements[pos];
}

static bool IsPackedDimension(const Expr* expr) {
  return expr != nullptr && expr->kind == ExprKind::kSelect &&
         expr->index != nullptr && expr->index_end != nullptr &&
         !expr->is_part_select_plus && !expr->is_part_select_minus;
}

DataType TypeSpelledBy(const Expr* elem) {
  if (elem->kind == ExprKind::kTypeRef && elem->type_value != nullptr)
    return *elem->type_value;
  std::vector<std::pair<Expr*, Expr*>> dims;
  const Expr* head = elem;
  for (; IsPackedDimension(head); head = head->base)
    dims.insert(dims.begin(), {head->index, head->index_end});
  if (head == nullptr || head->kind != ExprKind::kIdentifier) return {};
  DataType dt = TypeNameToDataType(head->text);
  if (dims.empty()) return dt;
  if (dt.packed_dim_left != nullptr)
    dims.push_back({dt.packed_dim_left, dt.packed_dim_right});
  dims.insert(dims.end(), dt.extra_packed_dims.begin(),
              dt.extra_packed_dims.end());
  dt.packed_dim_left = dims.front().first;
  dt.packed_dim_right = dims.front().second;
  dt.extra_packed_dims.assign(dims.begin() + 1, dims.end());
  return dt;
}

static void BindSpecializationTypeActuals(const ClassTypeInfo* spec,
                                          SimContext& ctx) {
  const ClassDecl* decl = spec->decl;
  for (size_t i = 0; i < decl->params.size(); ++i) {
    std::string_view pname = decl->params[i].first;
    if (decl->type_param_names.count(pname) == 0) continue;
    const DataType* actual = ActualForParam(*spec->param_actuals, i, pname);
    if (actual == nullptr || actual->kind == DataTypeKind::kImplicit) continue;
    ctx.BindScopeTypeActual(pname, actual);
  }
}

void BindClassScopeTypeActuals(const ClassTypeInfo* cls, const Expr* base,
                               SimContext& ctx, Arena& arena) {
  if (cls == nullptr || cls->decl == nullptr || base == nullptr) return;
  if (cls->param_actuals != nullptr) {
    BindSpecializationTypeActuals(cls, ctx);
    return;
  }
  const ClassDecl* decl = cls->decl;
  for (size_t i = 0; i < decl->params.size(); ++i) {
    std::string_view pname = decl->params[i].first;
    if (decl->type_param_names.count(pname) == 0) continue;
    const Expr* elem = SpecializationElement(*base, i, pname);
    if (elem == nullptr) continue;
    DataType dt = TypeSpelledBy(elem);
    if (dt.kind == DataTypeKind::kImplicit) continue;
    ctx.BindScopeTypeActual(pname, arena.Create<DataType>(dt));
  }
}

void BindStaticInitTypeActuals(const ClassTypeInfo* cls, SimContext& ctx) {
  if (cls == nullptr || cls->decl == nullptr) return;
  const ClassDecl* decl = cls->decl;
  for (size_t i = 0; i < decl->params.size(); ++i) {
    std::string_view pname = decl->params[i].first;
    if (decl->type_param_names.count(pname) == 0) continue;
    const DataType* actual = cls->param_actuals != nullptr
                                 ? ActualForParam(*cls->param_actuals, i, pname)
                                 : nullptr;
    if (actual == nullptr || actual->kind == DataTypeKind::kImplicit)
      actual = TypeParamActual(nullptr, decl, pname);
    if (actual != nullptr) ctx.BindScopeTypeActual(pname, actual);
  }
}

uint32_t ScopedTypeParamWidth(std::string_view name, SimContext& ctx) {
  if (const DataType* bound = ctx.FindScopeTypeActual(name))
    return DeclaredTypeWidth(*bound, ctx);
  const ClassTypeInfo* cls = ctx.CurrentMethodClass();
  if (cls == nullptr || cls->decl == nullptr ||
      cls->decl->type_param_names.count(name) == 0) {
    return 0;
  }
  const DataType* def = TypeParamActual(nullptr, cls->decl, name);
  return def != nullptr ? DeclaredTypeWidth(*def, ctx) : 0;
}

uint32_t SpecializationTypeParamWidth(const Expr* scope, SimContext& ctx,
                                      Arena& arena) {
  if (scope == nullptr || scope->kind != ExprKind::kMemberAccess ||
      !scope->is_scope_resolution || scope->rhs == nullptr ||
      scope->rhs->kind != ExprKind::kIdentifier) {
    return 0;
  }
  const ClassTypeInfo* spec = ScopeNamedSpecialization(scope->lhs, ctx, arena);
  if (spec == nullptr || spec->decl == nullptr ||
      spec->param_actuals == nullptr) {
    return 0;
  }
  const ClassDecl* decl = spec->decl;
  std::string_view pname = scope->rhs->text;
  if (decl->type_param_names.count(pname) == 0) return 0;
  for (size_t i = 0; i < decl->params.size(); ++i) {
    if (decl->params[i].first != pname) continue;
    const DataType* actual = ActualForParam(*spec->param_actuals, i, pname);
    if (actual == nullptr || actual->kind == DataTypeKind::kImplicit)
      actual = TypeParamActual(nullptr, decl, pname);
    return actual != nullptr ? DeclaredTypeWidth(*actual, ctx) : 0;
  }
  return 0;
}

}  // namespace delta
