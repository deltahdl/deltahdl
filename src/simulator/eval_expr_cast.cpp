#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/clocking.h"
#include "simulator/eval_array.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_string.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/sva_engine_sampling.h"
#include "simulator/variable.h"

namespace delta {

static bool IsRealCastTarget(std::string_view name) {
  return name == "real" || name == "realtime" || name == "shortreal";
}

static double ExtractDouble(const Logic4Vec& vec) {
  return RealVecToDouble(vec);
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
  // §6.24.1 (printed page 139): the value a variable of the casting type
  // holds once the operand is assigned to it, the integer's value as a real,
  // signed where the operand is. A shortreal is single precision in 32 bits
  // (MakeRealVec), which a double's pattern cut to 32 bits read back as 0.
  uint64_t raw = inner.ToUint64();
  auto d = static_cast<double>(raw);
  if (inner.is_signed && inner.width > 0 && inner.width < 64 &&
      ((raw >> (inner.width - 1)) & 1U) != 0U) {
    d = static_cast<double>(
        static_cast<int64_t>(raw | ~((uint64_t{1} << inner.width) - 1)));
  } else if (inner.is_signed && inner.width == 64) {
    d = static_cast<double>(static_cast<int64_t>(raw));
  }
  return MakeRealVec(arena, d, target_width);
}

// §6.24.1 with A.2.2.1: the key the type tables hold a named casting type
// under. A casting type written behind a class or a package, `C::T'(v)` or
// `p::S'(v)` (§8.23, §26.3), stands in the cast's rhs as a scope resolution
// and is held under "C::T"; a bare name inside a method names the running
// class's typedef, or that of a class enclosing it or one it extends, as it
// would in a declaration there, held under that class's key. Empty for a cast
// that names no type this way.
static std::string CastTypeKey(const Expr* expr, SimContext& ctx) {
  const Expr* rhs = expr->rhs;
  if (expr->text.empty()) {
    if (rhs == nullptr || rhs->kind != ExprKind::kMemberAccess ||
        !rhs->is_scope_resolution || rhs->lhs == nullptr ||
        rhs->rhs == nullptr || rhs->lhs->kind != ExprKind::kIdentifier ||
        rhs->rhs->kind != ExprKind::kIdentifier)
      return {};
    return std::string(rhs->lhs->text) + "::" + std::string(rhs->rhs->text);
  }
  for (const ClassTypeInfo* cls = ctx.CurrentMethodClass(); cls != nullptr;
       cls = cls->enclosing) {
    for (const ClassTypeInfo* c = cls; c != nullptr; c = c->parent) {
      std::string key = std::string(c->name) + "::" + std::string(expr->text);
      if (ctx.FindTypeWidth(key) > 0) return key;
    }
  }
  return std::string(expr->text);
}

// §6.24.1: what a variable of the casting type is, which the cast's result
// takes on: its width, whether it holds x and z (§6.11.2), and whether it is
// signed (§6.11.3). A keyword answers by itself; a typedef by what the design
// registered for its name, an enumeration by its base type (§6.19).
struct CastTarget {
  uint32_t width = 32;
  bool is_4state = true;
  bool is_signed = false;
};

static bool IsTwoStateKind(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kBit:
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
      return true;
    default:
      return false;
  }
}

static bool KeywordCastTarget(std::string_view name, CastTarget& out) {
  static constexpr std::string_view kTwoState[] = {"bit", "byte", "shortint",
                                                   "int", "longint"};
  static constexpr std::string_view kFourState[] = {"logic", "reg", "integer",
                                                    "time"};
  static constexpr std::string_view kSigned[] = {"byte", "shortint", "int",
                                                 "longint", "integer"};
  bool two = false;
  bool four = false;
  for (auto k : kTwoState) two = two || name == k;
  for (auto k : kFourState) four = four || name == k;
  if (!two && !four) return false;
  out.width = name == "time" ? 64 : CastTargetWidth(name);
  out.is_4state = four;
  out.is_signed = false;
  for (auto k : kSigned) out.is_signed = out.is_signed || name == k;
  return true;
}

static CastTarget ResolveCastTarget(std::string_view key, SimContext& ctx) {
  CastTarget t;
  if (KeywordCastTarget(key, t)) return t;
  t.width = ResolveCastWidth(key, ctx);
  t.is_signed = ctx.FindTypeSigned(key);
  if (const EnumTypeInfo* e = ctx.FindEnumType(key)) {
    t.is_4state = e->is_4state;
  } else {
    t.is_4state = !IsTwoStateKind(ctx.FindTypeKind(key));
  }
  return t;
}

// §6.11.3: the integer types signed unless declared unsigned.
static bool IsSignedByDefault(DataTypeKind kind) {
  return kind == DataTypeKind::kByte || kind == DataTypeKind::kShortint ||
         kind == DataTypeKind::kInt || kind == DataTypeKind::kLongint ||
         kind == DataTypeKind::kInteger;
}

// §6.23 with §6.24.1: the casting type a type reference stands for,
// `type(bit [11:0])'(v)` the data type written, `type(n)'(v)` the type n was
// declared with, and a typedef's name the type it names. False where `ref` is
// no type reference or names nothing this resolves, the cast then read as
// before.
static bool TypeRefCastTarget(const Expr* ref, SimContext& ctx,
                              CastTarget& out) {
  if (ref == nullptr || ref->kind != ExprKind::kTypeRef) return false;
  const DataType* written = ref->type_value;
  if (written != nullptr && written->kind != DataTypeKind::kNamed) {
    out.width = DeclaredTypeWidth(*written, ctx);
    out.is_4state = !IsTwoStateKind(written->kind);
    out.is_signed = written->is_signed || IsSignedByDefault(written->kind);
    return out.width > 0;
  }
  std::string_view name;
  if (written != nullptr && written->scope_name.empty()) {
    name = written->type_name;
  } else if (ref->lhs != nullptr && ref->lhs->kind == ExprKind::kIdentifier) {
    name = ref->lhs->text;
  }
  if (name.empty()) return false;
  // The parser reads `type(n)` as a type named n; a variable so named is the
  // expression whose type the reference takes.
  if (const Variable* var = ctx.FindVariable(name)) {
    out.width = var->value.width;
    out.is_4state = var->is_4state;
    out.is_signed = var->is_signed;
    return out.width > 0;
  }
  out = ResolveCastTarget(name, ctx);
  return true;
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
// §6.24.1: the result of a size cast is the value a packed [tw-1:0] vector
// would hold after being assigned the operand, and the operand's own
// (self-determined) signedness passes through unchanged. Widening a signed
// operand therefore replicates its sign bit -- in both the value and the x/z
// plane -- across the new high bits, exactly as an assignment of a signed
// source does; a narrowing cast or an unsigned operand simply masks to the
// target width.
static void WriteSizeCastWord(const Logic4Vec& inner, uint32_t tw,
                              Logic4Word& out_word) {
  uint64_t mask = tw >= 64 ? ~uint64_t{0} : (uint64_t{1} << tw) - 1;
  uint64_t aval = inner.words[0].aval;
  uint64_t bval = inner.words[0].bval;
  if (inner.is_signed && inner.width > 0 && inner.width < tw &&
      inner.width < 64) {
    uint64_t high_bits = mask & ~((uint64_t{1} << inner.width) - 1);
    if ((aval >> (inner.width - 1)) & 1) aval |= high_bits;
    if ((bval >> (inner.width - 1)) & 1) bval |= high_bits;
  }
  out_word.aval = aval & mask;
  out_word.bval = bval & mask;
}

static bool TrySizeCast(const Expr* expr, SimContext& ctx, Arena& arena,
                        Logic4Vec& out) {
  if (!expr->text.empty() || expr->rhs == nullptr || expr->lhs == nullptr)
    return false;
  if (expr->lhs->kind == ExprKind::kAssignmentPattern ||
      expr->rhs->kind == ExprKind::kTypeRef)
    return false;
  // A class's or a package's typedef, `C::T'(v)`, is a casting type rather
  // than a size, though it stands where a size expression does.
  if (std::string key = CastTypeKey(expr, ctx);
      !key.empty() && ctx.FindTypeWidth(key) > 0)
    return false;
  auto width_v = EvalExpr(expr->rhs, ctx, arena);
  if (!width_v.IsKnown()) return false;
  uint64_t w64 = width_v.ToUint64();
  if (w64 == 0 || w64 > 0xFFFF) return false;
  auto tw = static_cast<uint32_t>(w64);

  // §6.24.1 with §11.6.1: the operand is evaluated as if assigned to a
  // [tw-1:0] vector, so tw is its context width, and `10'(x * y)` multiplies
  // at 10 bits rather than at the wider operand's own.
  auto inner = EvalExpr(expr->lhs, ctx, arena, tw);
  auto result = MakeLogic4Vec(arena, tw);
  if (result.nwords > 0 && inner.nwords > 0)
    WriteSizeCastWord(inner, tw, result.words[0]);
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

// §16.5.1: the sampled value of a const cast expression is the current value
// of its argument, where every other expression of a concurrent assertion is
// evaluated over the sampled values of its variables. The property's sampling
// mode is lowered for the length of the argument's evaluation and put back
// after, so `const'(a)` reads a as it stands at the tick and `a` beside it
// reads the Preponed value; outside a property the mode is already off and the
// argument is read as any expression is.
static Logic4Vec EvalCastOperand(const Expr* operand, std::string_view cast,
                                 SimContext& ctx, Arena& arena) {
  if (cast != "const") return EvalExpr(operand, ctx, arena);
  auto& samples = ctx.AssertionSamples();
  bool sampling = samples.EvaluatingProperty();
  samples.SetEvaluatingProperty(false);
  auto inner = EvalExpr(operand, ctx, arena);
  samples.SetEvaluatingProperty(sampling);
  return inner;
}

// §10.9: the element count of each packed dimension of `dtype`, outermost
// first, where it is a packed array of logic, bit or reg whose bounds are
// known; empty for any other type.
static std::vector<uint32_t> PackedDimSpans(const DataType& dtype,
                                            SimContext& ctx, Arena& arena) {
  std::vector<uint32_t> spans;
  bool vector_kind = dtype.kind == DataTypeKind::kLogic ||
                     dtype.kind == DataTypeKind::kBit ||
                     dtype.kind == DataTypeKind::kReg;
  if (!vector_kind || dtype.packed_dim_left == nullptr) return spans;
  std::vector<std::pair<Expr*, Expr*>> dims{
      {dtype.packed_dim_left, dtype.packed_dim_right}};
  dims.insert(dims.end(), dtype.extra_packed_dims.begin(),
              dtype.extra_packed_dims.end());
  for (const auto& [left, right] : dims) {
    Logic4Vec l = EvalExpr(left, ctx, arena);
    Logic4Vec r = EvalExpr(right, ctx, arena);
    if (!l.IsKnown() || !r.IsKnown()) return {};
    int64_t lo = SelectBoundValue(l);
    int64_t hi = SelectBoundValue(r);
    spans.push_back(static_cast<uint32_t>(std::abs(hi - lo) + 1));
  }
  return spans;
}

// §10.9 (printed page 261): `T'{1,2}` is the value a variable of T holds once
// initialized with the pattern, wherever it is written. With T a structure,
// §10.9.2 places each member at its own offset and width, so `st'{3,4}` over
// two bytes is 16'h0304; with T a packed array, each item fills its element at
// the element's width -- 8'h12 for `typedef logic [1:0][3:0] T`. Evaluated as
// a bare pattern and then cut to T's width, the items were concatenated at
// their own 32 bits and only the last survived.
static bool TryTypedPatternCast(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out) {
  if (expr->lhs == nullptr || expr->lhs->kind != ExprKind::kAssignmentPattern)
    return false;
  std::string key = CastTypeKey(expr, ctx);
  if (const StructTypeInfo* layout = ctx.FindStructType(key)) {
    out = EvalStructPatternValue(expr->lhs, layout, ctx, arena);
    return true;
  }
  const DataType* dtype = ctx.FindTypeDeclaration(key);
  if (dtype == nullptr) return false;
  std::vector<uint32_t> spans = PackedDimSpans(*dtype, ctx, arena);
  auto value = EvalPackedArrayPattern(expr->lhs, spans, ctx.FindTypeWidth(key),
                                      ctx, arena);
  if (!value) return false;
  value->is_signed = ctx.FindTypeSigned(key);
  if (dtype->kind == DataTypeKind::kBit) CoerceTo2State(*value);
  out = *value;
  return true;
}

Logic4Vec EvalCast(const Expr* expr, SimContext& ctx, Arena& arena) {
  Logic4Vec stream_out;
  if (TryArrayBitStreamCast(expr, ctx, arena, stream_out)) return stream_out;
  Logic4Vec pattern_out;
  if (TryTypedPatternCast(expr, ctx, arena, pattern_out)) return pattern_out;

  Logic4Vec size_out;
  if (TrySizeCast(expr, ctx, arena, size_out)) return size_out;

  std::string_view type_name = expr->text;
  auto inner = EvalCastOperand(expr->lhs, type_name, ctx, arena);

  Logic4Vec kw_out;
  if (TryKeywordCast(type_name, inner, arena, kw_out)) return kw_out;

  CastTarget target;
  if (!TypeRefCastTarget(expr->rhs, ctx, target))
    target = ResolveCastTarget(CastTypeKey(expr, ctx), ctx);
  uint32_t target_width = target.width;

  if (inner.is_real != IsRealCastTarget(type_name)) {
    return CastRealConversion(inner, type_name, target_width, arena);
  }
  // §5.7.2 (printed page 80) has a cast convert a real literal to shortreal,
  // and §6.24.1 (printed 139) has the cast return what a variable of the
  // casting type holds after the expression is assigned to it, so
  // `shortreal'(0.5)` is the single-precision 0.5 and `real'(s)` the double
  // of a shortreal's value. The mask below is for an integral
  // value; it cut the double's pattern to 32 bits and dropped is_real, which
  // left `shortreal'(0.5) == 0.5` false and `s + 2.5` an integer's sum.
  if (inner.is_real) {
    return ConvertRealForKnownLhs(inner, true, target_width, arena);
  }
  // §6.24.1: the value a variable of the casting type holds once the operand
  // is assigned to it (§10.7): extended by the operand's own signedness or
  // truncated, x and z kept for a 4-state type and read as 0 for a 2-state
  // one (§6.3.2.2), and signed as the type is. Rebuilt from the operand's
  // numeric projection, every cast came out 2-state, unsigned and at most 64
  // bits wide: `integer'(4'bx)` was 0 and `byte'(8'h80) + 0` was 128.
  Logic4Vec result =
      OwnRhsWords(ResizeToWidth(inner, target_width, arena), arena);
  if (!target.is_4state) CoerceTo2State(result);
  result.is_signed = target.is_signed;
  return result;
}

}  // namespace delta
