#include <cstdint>
#include <functional>
#include <string>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"

namespace delta {

// Writes element i of the destination, counted from its leftmost, the value
// value_of(i), for every element.
static void FillElementsLeftToRight(
    const Stmt* stmt, const ArrayInfo& dst, SimContext& ctx,
    const std::function<Logic4Vec(uint32_t)>& value_of) {
  for (uint32_t i = 0; i < dst.size; ++i) {
    uint32_t di =
        dst.is_descending ? (dst.lo + dst.size - 1 - i) : (dst.lo + i);
    auto name = std::string(stmt->lhs->text) + "[" + std::to_string(di) + "]";
    auto* elem = ctx.FindVariable(name);
    if (!elem) continue;
    elem->value = value_of(i);
    elem->NotifyWatchers();
  }
}

// §6.24.3: a bit-stream cast whose casting type is an unpacked array, `e =
// B8'(x)` under `typedef bit B8 [8:1]`, turns its operand into a stream of
// bits and fills the destination's elements from it, left to right, the
// stream's most significant bits in the leftmost element, e[8]. Evaluated as
// a vector, the cast named no elements and left every one as it was. Taken
// only where the stream is exactly as wide as the one-dimensional fixed-size
// destination, which §6.24.3 requires of the cast.
static bool TryBitStreamCastToArray(const Stmt* stmt, const ArrayInfo& dst,
                                    SimContext& ctx, Arena& arena) {
  if (stmt->rhs->kind != ExprKind::kCast) return false;
  Logic4Vec stream = PackBitStreamOperand(stmt->rhs->lhs, ctx, arena);
  if (stream.width != dst.size * dst.elem_width) return false;
  FillElementsLeftToRight(stmt, dst, ctx, [&](uint32_t i) {
    return ExtractBitField(
        arena, stream, stream.width - (i + 1) * dst.elem_width, dst.elem_width);
  });
  return true;
}

// §5.9: a string literal assigned to an unpacked array of bytes, alone or cast
// to the array's type, fills it left-justified: its first character the
// leftmost element, the elements past its last zero.
static bool TryStringLiteralToArray(const Stmt* stmt, const ArrayInfo& dst,
                                    SimContext& ctx, Arena& arena) {
  const Expr* str = StringLiteralSource(stmt->rhs);
  if (str == nullptr) return false;
  Logic4Vec packed = EvalExpr(str, ctx, arena);
  FillElementsLeftToRight(stmt, dst, ctx, [&](uint32_t i) {
    return MakeLogic4VecVal(arena, dst.elem_width,
                            StringLiteralByteAt(packed, i));
  });
  return true;
}

bool TryFillArrayFromValue(const Stmt* stmt, const ArrayInfo& dst,
                           SimContext& ctx, Arena& arena) {
  // Both fills write a one-dimensional fixed-size unpacked array, neither
  // dynamic nor a queue.
  if (dst.is_dynamic || dst.is_queue || dst.dim_sizes.size() > 1) return false;
  return TryStringLiteralToArray(stmt, dst, ctx, arena) ||
         TryBitStreamCastToArray(stmt, dst, ctx, arena);
}

}  // namespace delta
