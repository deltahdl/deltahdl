#include <algorithm>
#include <functional>
#include <vector>

#include "elaborator/elaborator_helpers.h"
#include "elaborator/type_ref_walks.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

void AdoptReferencedType(DataType& dt, const DataType& type) {
  dt.kind = type.kind;
  dt.is_signed = type.is_signed;
  dt.type_name = type.type_name;
  dt.scope_name = type.scope_name;
  dt.outer_scope_names = type.outer_scope_names;
  dt.type_params = type.type_params;
  dt.packed_dim_left = type.packed_dim_left;
  dt.packed_dim_right = type.packed_dim_right;
  dt.extra_packed_dims = type.extra_packed_dims;
  dt.type_ref_expr = nullptr;
}

const Expr* TypeRefOperand(const Expr* written) {
  return written->kind == ExprKind::kTypeRef ? written->lhs : written;
}

static bool IsTypeRefArgument(const DataType& arg) {
  return arg.type_ref_expr != nullptr &&
         arg.type_ref_expr->kind == ExprKind::kTypeRef;
}

bool WritesTypeRefAmong(const std::vector<DataType>& args) {
  return std::ranges::any_of(args, [](const DataType& arg) {
    return IsTypeRefArgument(arg) || WritesTypeRefAmong(arg.type_params);
  });
}

bool WritesTypeRefArgument(const DataType& type) {
  return WritesTypeRefAmong(type.type_params);
}

void ResolveTypeRefArguments(std::vector<DataType>& args,
                             const std::function<void(DataType&)>& resolve) {
  for (DataType& arg : args) {
    if (IsTypeRefArgument(arg)) {
      const Expr& ref = *arg.type_ref_expr;
      DataType referenced;
      referenced.type_ref_expr = ref.lhs;
      if (ref.type_value != nullptr) referenced = *ref.type_value;
      referenced.type_ref_use = TypeRefUse::kArgument;
      resolve(referenced);
      referenced.type_ref_use = TypeRefUse::kDeclared;
      referenced.param_arg_name = arg.param_arg_name;
      if (referenced.type_ref_expr == nullptr) arg = referenced;
    }
    ResolveTypeRefArguments(arg.type_params, resolve);
  }
}

}  // namespace delta
