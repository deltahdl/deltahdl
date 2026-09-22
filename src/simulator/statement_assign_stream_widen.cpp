#include <cstdint>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

// Left-shift `stream` (stream_w bits) into a `total_w`-bit vector, padding the
// LSB side with zero bits. When no padding is needed the input is returned.
Logic4Vec RightPadStreamToWidth(const Logic4Vec& stream, uint32_t stream_w,
                                uint32_t total_w, Arena& arena) {
  if (total_w <= stream_w) return stream;
  auto widened = MakeLogic4Vec(arena, total_w);
  uint32_t shift = total_w - stream_w;
  for (uint32_t b = 0; b < stream_w; ++b) {
    uint32_t sw = b / 64, sb = b % 64;
    uint32_t dst_bit = shift + b;
    uint32_t dw = dst_bit / 64, db = dst_bit % 64;
    if (sw < stream.nwords) {
      if ((stream.words[sw].aval >> sb) & 1ull)
        widened.words[dw].aval |= uint64_t{1} << db;
      if ((stream.words[sw].bval >> sb) & 1ull)
        widened.words[dw].bval |= uint64_t{1} << db;
    }
  }
  return widened;
}

// §11.4.14 (printed page 291): when a streaming_concatenation is the source
// of an assignment and the target is a data object of bit-stream type, the
// stream is left-aligned in the target. A fixed-size target wider than the
// stream is filled with zero bits on the right (LSB side); a fixed-size
// target narrower than the stream is an error, reported at `loc`, the
// stream then assigned as it is. The rule is one for the statement
// assignment below and for a declaration's initializer, `bit [127:0] d =
// {<< 32 {a, b, c}}` (InitializeDeclVariable in statement_assign_decl.cpp),
// which took the stream as evaluated: the suite's
// 11.4.14.3--unpack_stream_pad-sim.sv read it right-aligned and its
// unpack_stream_inv.sv, `int d = {<<{a, b, c}}`, the §11.4.14.3 example's
// own error, went unreported.
Logic4Vec WidenStreamPackToFixedTarget(Logic4Vec stream, uint32_t target_width,
                                       SourceLoc loc, SimContext& ctx,
                                       Arena& arena) {
  uint32_t stream_width = stream.width;
  if (target_width == stream_width) return stream;
  if (target_width < stream_width) {
    ctx.GetDiag().Error(
        loc,
        "streaming concatenation source is wider than the fixed-size target",
        Subclause("11.4.14"));
    return stream;
  }
  return RightPadStreamToWidth(stream, stream_width, target_width, arena);
}

Logic4Vec ApplyStreamPackToTargetWidening(const Stmt* stmt, Logic4Vec rhs_val,
                                          SimContext& ctx, Arena& arena) {
  if (!stmt->rhs || stmt->rhs->kind != ExprKind::kStreamingConcat) {
    return rhs_val;
  }
  if (!stmt->lhs || stmt->lhs->kind != ExprKind::kIdentifier) {
    return rhs_val;
  }
  if (ctx.FindArrayInfo(stmt->lhs->text) || ctx.FindQueue(stmt->lhs->text) ||
      ctx.FindAssocArray(stmt->lhs->text)) {
    return rhs_val;
  }
  auto* var = ResolveLhsVariable(stmt->lhs, ctx);
  // §6.16: a string is dynamically sized, no fixed-size target to report on.
  if (!var || var->is_string || var->value.width == 0) return rhs_val;
  return WidenStreamPackToFixedTarget(rhs_val, var->value.width,
                                      stmt->lhs->range.start, ctx, arena);
}

}  // namespace delta
