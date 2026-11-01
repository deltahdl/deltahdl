// §6.20.2 (printed pages 126-127 of IEEE 1800-2023): the width and the
// value a package's or the compilation unit's parameter is given, each
// converted to the type its declaration writes.

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

// §6.20.2 (printed pages 126-127): whether a parameter's declaration fixes
// its width -- by a range or a type other than the implicit one, as
// HasDeclaredWidth (src/elaborator/const_eval_bits.cpp) reads it off a
// module's RtlirParamDecl -- and not by a real, shortreal or realtime type,
// whose value is a real that no vector width sizes (§6.12). One declared with
// neither takes the width of its value.
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

// The width a parameter's declaration fixes, its range evaluated in the
// package's frame where §6.20.1 lets a bound name an earlier parameter --
// `logic [N-1:0] M` after `int N = 12` is twelve bits -- and 0 where the
// declaration fixes none. Folded with no parameter in scope, `[N-1:0]` fell
// to the base type's one bit and M held a single bit.
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
