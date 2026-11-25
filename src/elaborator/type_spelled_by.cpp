#include "elaborator/type_spelled_by.h"

#include <cstddef>
#include <utility>
#include <vector>

#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

bool IsPackedDimension(const Expr* e) {
  return e->kind == ExprKind::kSelect && e->index_end != nullptr &&
         !e->is_part_select_plus && !e->is_part_select_minus;
}

void TakeSpecialization(const Expr& name, DataType& type) {
  type.param_assignment_written = name.has_param_spec;
  if (!name.has_param_spec) return;
  type.type_params.clear();
  for (std::size_t i = 0; i < name.elements.size(); ++i) {
    Expr* const kValue = name.elements[i];
    DataType arg;
    if (kValue != nullptr) arg = TypeSpelledBy(kValue);
    const bool kMayBeASelectedValue =
        arg.kind == DataTypeKind::kNamed && kValue->kind == ExprKind::kSelect;
    if (arg.kind == DataTypeKind::kImplicit || kMayBeASelectedValue)
      arg.type_ref_expr = kValue;
    arg.param_arg_name = name.arg_names[i];
    type.type_params.push_back(arg);
  }
}

DataType SpecializedScope(const DataType& path) {
  DataType scope;
  scope.kind = DataTypeKind::kNamed;
  scope.type_name = path.type_name;
  scope.scope_name = path.scope_name;
  scope.type_params = path.type_params;
  return scope;
}

void EnterScopeOfName(const Expr& access, DataType& type) {
  if (type.param_assignment_written)
    type.specialized_scopes.push_back(SpecializedScope(type));
  if (!type.scope_name.empty())
    type.outer_scope_names.push_back(type.scope_name);
  type.scope_name = type.type_name;
  type.scope_param_assignment_written = type.param_assignment_written;
  type.type_name = access.rhs->text;
  TakeSpecialization(access, type);
}

void EnterName(const Expr& name, DataType& type) {
  if (name.kind == ExprKind::kIdentifier) {
    type.kind = DataTypeKind::kNamed;
    type.scope_name = name.scope_prefix;
    type.type_name = name.text;
    TakeSpecialization(name, type);
  } else if (name.kind == ExprKind::kMemberAccess && name.is_scope_resolution) {
    EnterName(*name.lhs, type);
    EnterScopeOfName(name, type);
  }
}

DataType HeadSpelledBy(const Expr& head) {
  if (head.kind == ExprKind::kTypeRef && head.type_value != nullptr)
    return *head.type_value;
  DataType type;
  EnterName(head, type);
  if (type.kind == DataTypeKind::kImplicit) return {};
  DataType builtin = TypeNameToDataType(type.type_name);
  const bool kBuiltin =
      type.scope_name.empty() && builtin.kind != DataTypeKind::kNamed;
  return kBuiltin ? builtin : type;
}

}  // namespace

DataType TypeSpelledBy(const Expr* written) {
  std::vector<std::pair<Expr*, Expr*>> dims;
  const Expr* head = written;
  for (; IsPackedDimension(head); head = head->base)
    dims.insert(dims.begin(), {head->index, head->index_end});
  DataType type = HeadSpelledBy(*head);
  if (dims.empty() || type.kind == DataTypeKind::kImplicit) return type;
  type.packed_dim_left = dims.front().first;
  type.packed_dim_right = dims.front().second;
  type.extra_packed_dims.assign(dims.begin() + 1, dims.end());
  return type;
}

}  // namespace delta
