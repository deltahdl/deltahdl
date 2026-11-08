#include <algorithm>
#include <cstdint>
#include <cstring>
#include <optional>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/evaluation_internal.h"
#include "simulator/pattern_match.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"

namespace delta {

static Logic4Vec CombineBranches(Logic4Vec tv, Logic4Vec fv, Arena& arena) {
  uint32_t width = (tv.width > fv.width) ? tv.width : fv.width;
  auto result = MakeLogic4Vec(arena, width);
  for (uint32_t i = 0; i < result.nwords; ++i) {
    auto tw = (i < tv.nwords) ? tv.words[i] : Logic4Word{};
    auto fw = (i < fv.nwords) ? fv.words[i] : Logic4Word{};
    result.words[i].bval = tw.bval | fw.bval | (tw.aval ^ fw.aval);
    result.words[i].aval = (tw.aval & fw.aval) | result.words[i].bval;
  }
  if (tv.is_real || fv.is_real) result.is_real = true;
  return result;
}
static double TernaryOperandToDouble(const Logic4Vec& v) {
  if (v.is_real) return RealVecToDouble(v);
  if (v.is_signed && v.width > 0 && v.width < 64) {
    uint64_t raw = v.ToUint64();
    if ((raw >> (v.width - 1)) & 1u) raw |= ~((uint64_t{1} << v.width) - 1);
    return static_cast<double>(static_cast<int64_t>(raw));
  }
  if (v.is_signed)
    return static_cast<double>(static_cast<int64_t>(v.ToUint64()));
  return static_cast<double>(v.ToUint64());
}
static Logic4Vec MakeRealVec(Arena& arena, double d) {
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  auto r = MakeLogic4VecVal(arena, 64, bits);
  r.is_real = true;
  return r;
}
static Logic4Vec StructDefault(const StructTypeInfo& layout, Arena& arena) {
  Logic4Vec value = MakeLogic4Vec(arena, layout.total_width);
  for (const StructFieldInfo& field : layout.fields) {
    if (!Is4stateType(field.type_kind)) continue;
    for (uint32_t b = field.bit_offset; b < field.bit_offset + field.width;
         ++b) {
      value.words[b / 64].aval |= uint64_t{1} << (b % 64);
      value.words[b / 64].bval |= uint64_t{1} << (b % 64);
    }
  }
  return value;
}

static std::optional<Logic4Vec> NonintegralDefault(const Expr* operand,
                                                   const Logic4Vec& value,
                                                   SimContext& ctx,
                                                   Arena& arena) {
  if (value.is_string) {
    Logic4Vec empty = StringToLogic4Vec(arena, "");
    empty.is_string = true;
    return empty;
  }
  if (operand->kind != ExprKind::kIdentifier) return std::nullopt;
  if (!ctx.GetVariableClassType(operand->text).empty())
    return MakeLogic4VecVal(arena, value.width, kNullClassHandle);
  const StructTypeInfo* layout = ctx.GetVariableStructType(operand->text);
  if (layout == nullptr || layout->is_packed) return std::nullopt;
  return StructDefault(*layout, arena);
}

static Logic4Vec RealBranchesMerged(const Logic4Vec& tv, const Logic4Vec& fv,
                                    Arena& arena) {
  double td = TernaryOperandToDouble(tv);
  double fd = TernaryOperandToDouble(fv);
  return MakeRealVec(arena, td == fd ? td : 0.0);
}

static Logic4Vec EvalTernaryUnknownCond(const Expr* expr, SimContext& ctx,
                                        Arena& arena, uint32_t context_width) {
  auto tv = EvalExpr(expr->true_expr, ctx, arena, context_width);
  auto fv = EvalExpr(expr->false_expr, ctx, arena, context_width);
  if (tv.is_real || fv.is_real) return RealBranchesMerged(tv, fv, arena);
  bool result_signed = tv.is_signed && fv.is_signed;
  uint32_t width = (tv.width > fv.width) ? tv.width : fv.width;
  if (context_width > width) width = context_width;
  if (tv.width < width) tv = ExtendVec(tv, width, result_signed, arena);
  if (fv.width < width) fv = ExtendVec(fv, width, result_signed, arena);
  const bool kEqual =
      !HasUnknownBits(tv) && !HasUnknownBits(fv) && EvalCaseEquality(tv, fv);
  if (auto fallback = NonintegralDefault(expr->true_expr, tv, ctx, arena))
    return kEqual ? tv : *fallback;
  Logic4Vec result;
  if (kEqual) {
    tv.is_signed = result_signed;
    result = tv;
  } else {
    result = CombineBranches(tv, fv, arena);
    result.is_signed = result_signed;
  }
  if (context_width > 0 && result.width > context_width) {
    result = ResizeToWidth(result, context_width, arena);
  }
  return result;
}
static Logic4Vec IntegralToReal(const Logic4Vec& v, Arena& arena) {
  double d = 0.0;
  if (v.is_signed && v.width > 0 && v.width < 64) {
    uint64_t raw = v.ToUint64();
    if ((raw >> (v.width - 1)) & 1u) raw |= ~((uint64_t{1} << v.width) - 1);
    d = static_cast<double>(static_cast<int64_t>(raw));
  } else if (v.is_signed) {
    d = static_cast<double>(static_cast<int64_t>(v.ToUint64()));
  } else {
    d = static_cast<double>(v.ToUint64());
  }
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  auto r = MakeLogic4VecVal(arena, 64, bits);
  r.is_real = true;
  return r;
}

static Logic4Vec SizeTernaryResult(Logic4Vec v, uint32_t width, bool is_signed,
                                   uint32_t context_width, Arena& arena) {
  if (v.is_real) return v;
  v.is_signed = is_signed;
  if (v.width < width) v = ExtendVec(v, width, is_signed, arena);
  if (context_width > 0 && v.width > context_width)
    v = ResizeToWidth(v, context_width, arena);
  return v;
}

static Logic4Vec EvalTernaryBindingPredicate(const Expr* expr, SimContext& ctx,
                                             Arena& arena,
                                             uint32_t context_width) {
  ctx.PushScope();
  Truth predicate = EvalPredicateTruth(expr->condition, ctx, arena);
  if (predicate == Truth::kFalse) BindPatternTypes(expr->condition, ctx, arena);
  const bool kSigned = SimSelfSigned(expr->true_expr, ctx) &&
                       SimSelfSigned(expr->false_expr, ctx);
  const uint32_t kWidth =
      std::max({SimSelfWidth(expr->true_expr, ctx),
                SimSelfWidth(expr->false_expr, ctx), context_width});
  Logic4Vec tv;
  if (predicate != Truth::kFalse) {
    tv = SizeTernaryResult(EvalExpr(expr->true_expr, ctx, arena, context_width),
                           kWidth, kSigned, context_width, arena);
  }
  ctx.PopScope();
  if (predicate == Truth::kTrue) return tv;
  Logic4Vec fv =
      SizeTernaryResult(EvalExpr(expr->false_expr, ctx, arena, context_width),
                        kWidth, kSigned, context_width, arena);
  return predicate == Truth::kFalse ? fv : CombineBranches(tv, fv, arena);
}

Logic4Vec EvalTernary(const Expr* expr, SimContext& ctx, Arena& arena,
                      uint32_t context_width, bool unsigned_context) {
  if (PatternBindsIdentifiers(expr->condition))
    return EvalTernaryBindingPredicate(expr, ctx, arena, context_width);
  const Truth kPredicate = TruthOf(EvalExpr(expr->condition, ctx, arena));
  if (kPredicate == Truth::kAmbiguous) {
    return EvalTernaryUnknownCond(expr, ctx, arena, context_width);
  }
  const bool kChoosesFirst = kPredicate == Truth::kTrue;
  const Expr* other_expr = kChoosesFirst ? expr->false_expr : expr->true_expr;
  const bool kUnsigned = unsigned_context ||
                         !SimSelfSigned(expr->true_expr, ctx) ||
                         !SimSelfSigned(expr->false_expr, ctx);
  auto chosen =
      EvalExprInContext(kChoosesFirst ? expr->true_expr : expr->false_expr, ctx,
                        arena, context_width, kUnsigned);
  if (kUnsigned && !chosen.is_real) chosen.is_signed = false;
  const bool kReal = chosen.is_real || SimSelfReal(other_expr, ctx);
  if (kReal) {
    if (!chosen.is_real) chosen = IntegralToReal(chosen, arena);
    return chosen;
  }
  uint32_t width =
      std::max({chosen.width, SimSelfWidth(other_expr, ctx), context_width});
  Logic4Vec result = chosen.width < width
                         ? ExtendVec(chosen, width, chosen.is_signed, arena)
                         : chosen;
  if (context_width > 0 && result.width > context_width) {
    result = ResizeToWidth(result, context_width, arena);
  }
  return result;
}

}  // namespace delta
