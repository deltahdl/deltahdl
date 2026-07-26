#include <algorithm>
#include <cmath>
#include <cstring>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulator/class_object.h"
#include "simulator/clocking.h"
#include "simulator/eval_array.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"

namespace delta {

static bool IsRealCastTarget(std::string_view name) {
  return name == "real" || name == "realtime" || name == "shortreal";
}

static double ExtractDouble(const Logic4Vec& vec) {
  double d = 0.0;
  uint64_t bits = vec.ToUint64();
  std::memcpy(&d, &bits, sizeof(double));
  return d;
}

// §6.24.3: packs the elements of a bit-stream source into a single packed
// value. The first element (index 0 of a fixed unpacked, dynamic, or queue
// array) takes the most significant bit positions of the result. The aval
// and bval (4-state mask) are propagated independently so a source carrying
// any X or Z bit yields a 4-state packed value.
//
// BitStreamPack bundles the packing layout for one unpacked array: the source
// array's name and shape (`info`) plus the element count, total packed width,
// and the per-element bit mask derived from the element width.
struct BitStreamPack {
  std::string_view name;
  const ArrayInfo& info;
  uint32_t elem_count;
  uint32_t total_bits;
  uint32_t elem_mask;
};

// Accumulated packed result: the aval/bval mask pair of the packed value.
struct PackedBits {
  uint64_t aval = 0;
  uint64_t bval = 0;
};

// Packs the low word of each queue element into the accumulated result using
// the element-major shift expected by PackArrayBitStream (element 0 most
// significant).
static void PackQueueElements(const BitStreamPack& pack, SimContext& ctx,
                              PackedBits& out) {
  auto* q = ctx.FindQueue(pack.name);
  if (!q) return;
  for (uint32_t i = 0; i < pack.elem_count; ++i) {
    const auto& v = q->elements[i];
    uint64_t aval = v.nwords > 0 ? v.words[0].aval : 0;
    uint64_t bval = v.nwords > 0 ? v.words[0].bval : 0;
    uint32_t shift = pack.total_bits - (i + 1) * pack.info.elem_width;
    out.aval |= (aval & pack.elem_mask) << shift;
    out.bval |= (bval & pack.elem_mask) << shift;
  }
}

// Packs the low word of each fixed-unpacked-array element into `out` using the
// same element-major shift.
static void PackFixedArrayElements(const BitStreamPack& pack, SimContext& ctx,
                                   PackedBits& out) {
  for (uint32_t i = 0; i < pack.elem_count; ++i) {
    uint32_t idx = pack.info.lo + i;
    auto elem_name = std::string(pack.name) + "[" + std::to_string(idx) + "]";
    auto* elem = ctx.FindVariable(elem_name);
    if (!elem) continue;
    uint64_t aval = elem->value.nwords > 0 ? elem->value.words[0].aval : 0;
    uint64_t bval = elem->value.nwords > 0 ? elem->value.words[0].bval : 0;
    uint32_t shift = pack.total_bits - (i + 1) * pack.info.elem_width;
    out.aval |= (aval & pack.elem_mask) << shift;
    out.bval |= (bval & pack.elem_mask) << shift;
  }
}

static Logic4Vec PackArrayBitStream(std::string_view name,
                                    const ArrayInfo& info, SimContext& ctx,
                                    Arena& arena) {
  // §6.24.3: a queue and a dynamic array are both dynamically sized bit-stream
  // types, and at runtime both keep their elements in a QueueObject rather than
  // in individually named element variables. A fixed-size unpacked array has no
  // such backing store. Pack from the queue whenever one backs this name so the
  // element count and values are taken from the live queue; index 0 still
  // occupies the most significant bits either way.
  auto* q = ctx.FindQueue(name);
  uint32_t elem_count = info.size;
  if (q) elem_count = static_cast<uint32_t>(q->elements.size());
  uint32_t total_bits = elem_count * info.elem_width;
  uint32_t elem_mask = info.elem_width >= 64
                           ? ~uint32_t{0}
                           : (uint32_t{1} << info.elem_width) - 1;
  BitStreamPack pack{name, info, elem_count, total_bits, elem_mask};
  PackedBits packed;
  if (q) {
    PackQueueElements(pack, ctx, packed);
  } else {
    PackFixedArrayElements(pack, ctx, packed);
  }
  auto vec = MakeLogic4Vec(arena, total_bits);
  if (vec.nwords > 0) {
    uint64_t width_mask =
        total_bits >= 64 ? ~uint64_t{0} : (uint64_t{1} << total_bits) - 1;
    vec.words[0].aval = packed.aval & width_mask;
    vec.words[0].bval = packed.bval & width_mask;
  }
  return vec;
}

// §6.24.3: packs an associative-array bit-stream source. Items are packed in
// index-sorted order -- the underlying std::map keeps its keys ordered -- with
// the first key's element occupying the most significant bits, mirroring the
// queue/array packing. Both halves of the 4-state encoding are carried so an
// x/z in any element propagates into the packed value.
static Logic4Vec PackAssocBitStream(const AssocArrayObject& aa, Arena& arena) {
  uint32_t elem_width = aa.elem_width;
  uint32_t elem_count = aa.Size();
  uint32_t total_bits = elem_count * elem_width;
  uint32_t elem_mask =
      elem_width >= 64 ? ~uint32_t{0} : (uint32_t{1} << elem_width) - 1;
  PackedBits packed;
  uint32_t i = 0;
  auto pack_one = [&](const Logic4Vec& v) {
    uint64_t aval = v.nwords > 0 ? v.words[0].aval : 0;
    uint64_t bval = v.nwords > 0 ? v.words[0].bval : 0;
    uint32_t shift = total_bits - (i + 1) * elem_width;
    packed.aval |= (aval & elem_mask) << shift;
    packed.bval |= (bval & elem_mask) << shift;
    ++i;
  };
  if (aa.is_string_key) {
    for (const auto& entry : aa.str_data) pack_one(entry.second);
  } else {
    for (const auto& entry : aa.int_data) pack_one(entry.second);
  }
  auto vec = MakeLogic4Vec(arena, total_bits);
  if (vec.nwords > 0) {
    uint64_t width_mask =
        total_bits >= 64 ? ~uint64_t{0} : (uint64_t{1} << total_bits) - 1;
    vec.words[0].aval = packed.aval & width_mask;
    vec.words[0].bval = packed.bval & width_mask;
  }
  return vec;
}

static Logic4Vec CastRealConversion(const Logic4Vec& inner,
                                    std::string_view type_name,
                                    uint32_t target_width, Arena& arena) {
  if (inner.is_real && !IsRealCastTarget(type_name)) {
    auto val = static_cast<uint64_t>(
        static_cast<int64_t>(std::llround(ExtractDouble(inner))));
    if (target_width < 64) val &= (uint64_t{1} << target_width) - 1;
    auto result = MakeLogic4VecVal(arena, target_width, val);
    result.is_signed = true;
    return result;
  }
  auto d = static_cast<double>(inner.ToUint64());
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  auto result = MakeLogic4VecVal(arena, target_width, bits);
  result.is_real = true;
  return result;
}

uint32_t ResolveCastWidth(std::string_view type_name, SimContext& ctx) {
  uint32_t w = CastTargetWidth(type_name);
  if (w > 0) return w;

  uint32_t tw = ctx.FindTypeWidth(type_name);
  return tw > 0 ? tw : 32;
}

// §6.24.3 bit-stream cast: when the cast source names an unpacked/dynamic/queue
// array or an associative array, packs it and width-masks into the destination,
// carrying both halves of the 4-state encoding so any X/Z in the source
// propagates. Returns true and fills `out` when `expr` named such a source.
static bool TryArrayBitStreamCast(const Expr* expr, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kIdentifier) return false;
  auto name = expr->lhs->text;
  auto* arr_info = ctx.FindArrayInfo(name);
  // §6.24.3: a queue is a bit-stream type, but unlike a fixed unpacked array or
  // a dynamic array it registers no ArrayInfo -- only a QueueObject. Synthesize
  // the packing shape from the queue so a bare queue can be a bit-stream cast
  // source and be packed like any other dynamically sized array.
  ArrayInfo synth;
  if (!arr_info) {
    if (auto* q = ctx.FindQueue(name)) {
      synth.is_queue = true;
      synth.elem_width = q->elem_width;
      synth.size = static_cast<uint32_t>(q->elements.size());
      arr_info = &synth;
    }
  }

  Logic4Vec inner;
  if (arr_info &&
      (arr_info->size > 0 || arr_info->is_queue || arr_info->is_dynamic)) {
    inner = PackArrayBitStream(name, *arr_info, ctx, arena);
  } else if (auto* aa = ctx.FindAssocArray(name)) {
    // §6.24.3: an associative array is a legal bit-stream cast source (it is
    // illegal only as a destination), packed in index-sorted order.
    inner = PackAssocBitStream(*aa, arena);
  } else {
    return false;
  }

  uint32_t target_width = ResolveCastWidth(expr->text, ctx);
  auto result = MakeLogic4Vec(arena, target_width);
  if (result.nwords > 0 && inner.nwords > 0) {
    uint64_t width_mask =
        target_width >= 64 ? ~uint64_t{0} : (uint64_t{1} << target_width) - 1;
    result.words[0].aval = inner.words[0].aval & width_mask;
    result.words[0].bval = inner.words[0].bval & width_mask;
  }
  out = result;
  return true;
}

// §6.24.1: a numeric size cast (a constant_primary casting type) records its
// target width in an expression node rather than a type-name string: the parser
// leaves `text` empty and carries the width expression in `rhs` and the operand
// in `lhs`. Evaluate that width and pad/truncate the operand to it, letting the
// operand's own signedness pass through unchanged. Returns true and fills `out`
// when `expr` is such a cast. A cast that names a type (nonempty `text`), an
// assignment-pattern cast (`lhs` is an assignment pattern), or a type-reference
// cast (`rhs` is a type reference) is not a size cast and is left to the
// caller.
static bool TrySizeCast(const Expr* expr, SimContext& ctx, Arena& arena,
                        Logic4Vec& out) {
  if (!expr->text.empty() || expr->rhs == nullptr || expr->lhs == nullptr)
    return false;
  if (expr->lhs->kind == ExprKind::kAssignmentPattern ||
      expr->rhs->kind == ExprKind::kTypeRef)
    return false;
  auto width_v = EvalExpr(expr->rhs, ctx, arena);
  if (!width_v.IsKnown()) return false;
  uint64_t w64 = width_v.ToUint64();
  if (w64 == 0 || w64 > 0xFFFF) return false;
  uint32_t tw = static_cast<uint32_t>(w64);

  auto inner = EvalExpr(expr->lhs, ctx, arena);
  auto result = MakeLogic4Vec(arena, tw);
  uint64_t mask = tw >= 64 ? ~uint64_t{0} : (uint64_t{1} << tw) - 1;
  if (result.nwords > 0 && inner.nwords > 0) {
    uint64_t aval = inner.words[0].aval;
    uint64_t bval = inner.words[0].bval;
    // §6.24.1: the result is the value a packed [tw-1:0] vector would hold
    // after being assigned the operand, and the operand's own (self-determined)
    // signedness passes through unchanged. Widening a signed operand therefore
    // replicates its sign bit -- in both the value and the x/z plane -- across
    // the new high bits, exactly as an assignment of a signed source does; a
    // narrowing cast or an unsigned operand simply masks to the target width.
    if (inner.is_signed && inner.width > 0 && inner.width < tw &&
        inner.width < 64) {
      uint64_t high_bits = mask & ~((uint64_t{1} << inner.width) - 1);
      if ((aval >> (inner.width - 1)) & 1) aval |= high_bits;
      if ((bval >> (inner.width - 1)) & 1) bval |= high_bits;
    }
    result.words[0].aval = aval & mask;
    result.words[0].bval = bval & mask;
  }
  result.is_signed = inner.is_signed;
  out = result;
  return true;
}

// Handles the signedness/const/void cast keywords that simply re-tag or empty
// the inner value. Returns true and fills `out` when `type_name` was one of
// those keywords. `inner` may be mutated in place for the signedness cases.
static bool TryKeywordCast(std::string_view type_name, Logic4Vec& inner,
                           Arena& arena, Logic4Vec& out) {
  if (type_name == "signed") {
    inner.is_signed = true;
    out = inner;
    return true;
  }
  if (type_name == "unsigned") {
    inner.is_signed = false;
    out = inner;
    return true;
  }
  if (type_name == "const") {
    out = inner;
    return true;
  }
  if (type_name == "void") {
    out = MakeLogic4Vec(arena, 0);
    return true;
  }
  return false;
}

Logic4Vec EvalCast(const Expr* expr, SimContext& ctx, Arena& arena) {
  Logic4Vec stream_out;
  if (TryArrayBitStreamCast(expr, ctx, arena, stream_out)) return stream_out;

  Logic4Vec size_out;
  if (TrySizeCast(expr, ctx, arena, size_out)) return size_out;

  auto inner = EvalExpr(expr->lhs, ctx, arena);
  std::string_view type_name = expr->text;

  Logic4Vec kw_out;
  if (TryKeywordCast(type_name, inner, arena, kw_out)) return kw_out;

  uint32_t target_width = ResolveCastWidth(type_name, ctx);

  if (inner.is_real != IsRealCastTarget(type_name)) {
    return CastRealConversion(inner, type_name, target_width, arena);
  }
  uint64_t val = inner.ToUint64();
  if (target_width < 64) val &= (uint64_t{1} << target_width) - 1;
  return MakeLogic4VecVal(arena, target_width, val);
}

}  // namespace delta
