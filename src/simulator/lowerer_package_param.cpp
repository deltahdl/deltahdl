#include "simulator/lowerer_package_param.h"

#include <cstdint>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

static bool ParamDeclaresAWidth(const ModuleItem* item) {
  const DataType& type = item->data_type;
  if (type.packed_dim_left == nullptr && type.kind == DataTypeKind::kImplicit)
    return false;
  return type.kind != DataTypeKind::kReal &&
         type.kind != DataTypeKind::kShortreal &&
         type.kind != DataTypeKind::kRealtime;
}

uint32_t DeclaredParamStorageWidth(const ModuleItem* item, SimContext& ctx) {
  if (!ParamDeclaresAWidth(item)) return 0;
  const DataType& type = item->data_type;
  if (type.packed_dim_left != nullptr) return PackedDimProduct(type);
  return DeclaredTypeWidth(type, ctx);
}

static uint32_t DeclaredParamWidth(const ModuleItem* item, SimContext& ctx,
                                   Arena& arena) {
  if (!ParamDeclaresAWidth(item) || DeclaredTypeIsReal(item->data_type, ctx))
    return 0;
  const DataType& type = item->data_type;
  if (type.packed_dim_left != nullptr)
    return EvalFormalArgWidth(type, ctx, arena);
  return DeclaredTypeWidth(type, ctx);
}

Logic4Vec HeldAtWidth(Logic4Vec value, uint32_t width, const Variable& var,
                      Arena& arena) {
  if (value.is_real) value = ConvertRealForKnownLhs(value, false, width, arena);
  value = OwnRhsWords(ResizeToWidth(value, width, arena), arena);
  if (!var.is_4state) CoerceTo2State(value);
  value.is_signed = var.is_signed;
  return value;
}

void InitPackageParam(const ModuleItem* item, Variable* var, SimContext& ctx,
                      Arena& arena) {
  uint32_t width = DeclaredParamWidth(item, ctx, arena);
  if (width == 0) {
    var->value = ToDeclaredReal(EvalExpr(item->init_expr, ctx, arena),
                                &item->data_type, ctx, arena);
    return;
  }
  var->value = HeldAtWidth(EvalExpr(item->init_expr, ctx, arena, width), width,
                           *var, arena);
}

}  // namespace delta
