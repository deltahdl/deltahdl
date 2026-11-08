#include <cstdint>
#include <cstdlib>
#include <string>
#include <utility>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/assoc_index_type.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

bool IsAssocIndexDim(const Expr* dim, SimContext& ctx) {
  if (!dim) return false;
  if (dim->kind == ExprKind::kTypeRef) return true;
  if (const std::string kKey = ScopedTypeKey(dim); !kKey.empty()) {
    return ctx.FindTypeWidth(kKey) != 0 || ctx.FindClassType(kKey) != nullptr;
  }
  if (dim->kind != ExprKind::kIdentifier) return false;
  if (dim->text == "*") return true;
  if (TypeNameToDataType(dim->text).kind != DataTypeKind::kNamed) return true;
  if (ctx.FindClassType(dim->text) != nullptr) return true;
  return ctx.FindTypeWidth(dim->text) != 0;
}

AssocArraySpec AssocIndexSpecOfType(const DataType& index_type,
                                    bool elem_4state, SimContext& ctx) {
  AssocArraySpec spec;
  spec.is_4state = elem_4state;
  if (index_type.kind != DataTypeKind::kNamed) {
    if (uint32_t width = EvalTypeWidth(index_type); width != 0)
      spec.index_width = width;
    spec.is_index_signed = IsSignedType(index_type, {});
  } else if (ctx.FindClassType(index_type.type_name) != nullptr) {
    spec.index_width = 64;
    spec.index_class = index_type.type_name;
  } else {
    spec.index_type_name = index_type.type_name;
    if (uint32_t named = ctx.FindTypeWidth(index_type.type_name); named != 0)
      spec.index_width = named;
  }
  return spec;
}

DataType AssocIndexType(const Expr* dim, SimContext& ctx) {
  if (dim->kind == ExprKind::kTypeRef) return *dim->type_value;
  std::string key = ScopedTypeKey(dim);
  if (key.empty()) return TypeNameToDataType(dim->text);
  DataType named;
  named.kind = DataTypeKind::kNamed;
  named.type_name = *ctx.GetArena().Create<std::string>(std::move(key));
  return named;
}

bool IsStringIndexDim(const Expr* dim, SimContext& ctx) {
  return AssocIndexType(dim, ctx).kind == DataTypeKind::kString;
}

AssocArraySpec AssocIndexSpec(const Expr* dim, bool elem_4state,
                              SimContext& ctx) {
  AssocArraySpec spec =
      AssocIndexSpecOfType(AssocIndexType(dim, ctx), elem_4state, ctx);
  spec.is_wildcard = dim->text == "*";
  if (dim->op == TokenKind::kKwUnsigned) spec.is_index_signed = false;
  if (dim->op == TokenKind::kKwSigned) spec.is_index_signed = true;
  if (!dim->elements.empty()) {
    uint32_t width = 1;
    for (const Expr* packed : dim->elements) {
      auto msb = static_cast<int64_t>(
          EvalExpr(packed->lhs, ctx, ctx.GetArena()).ToUint64());
      auto lsb = static_cast<int64_t>(
          EvalExpr(packed->rhs, ctx, ctx.GetArena()).ToUint64());
      width *= static_cast<uint32_t>(std::abs(msb - lsb) + 1);
    }
    spec.index_width = width;
  }
  return spec;
}

}  // namespace delta
