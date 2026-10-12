#include <algorithm>
#include <cstdint>
#include <cstring>
#include <optional>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/evaluation_internal.h"
#include "simulator/pattern_match.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"

namespace delta {

// §11.4.11: the conditional operator. A determinate predicate evaluates the
// operand it selects and never the other; an ambiguous one evaluates both and
// returns either where they are logically equal, and otherwise combines
// integral ones bit by bit, compares real ones numerically and gives any other
// type its Table 7-1 default.

static Logic4Vec CombineBranches(Logic4Vec tv, Logic4Vec fv, Arena& arena) {
  uint32_t width = (tv.width > fv.width) ? tv.width : fv.width;
  auto result = MakeLogic4Vec(arena, width);
  for (uint32_t i = 0; i < result.nwords; ++i) {
    auto tw = (i < tv.nwords) ? tv.words[i] : Logic4Word{};
    auto fw = (i < fv.nwords) ? fv.words[i] : Logic4Word{};
    // §11.4.11 Table 11-22: result is 0 iff both 0, 1 iff both 1, else x. Under
    // the canonical encoding x=(aval=1,bval=1), so every unknown result bit
    // sets aval as well as bval.
    result.words[i].bval = tw.bval | fw.bval | (tw.aval ^ fw.aval);
    result.words[i].aval = (tw.aval & fw.aval) | result.words[i].bval;
  }
  if (tv.is_real || fv.is_real) result.is_real = true;
  return result;
}
// Read a conditional operand as a floating-point value: a real vector holds a
// double (or float, when 32-bit) bit pattern; an integral vector contributes
// its numeric value, sign-extended when signed.
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
// Table 7-1's default for each member of the unpacked structure `layout`:
// x in every bit of a 4-state member, 0 in a 2-state one's.
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

// §11.4.11 with Table 7-1: the value a conditional over nonintegral operands
// that are not logically equal gives under an ambiguous predicate -- "" for a
// string, null for a class handle, each member's default for an unpacked
// structure -- and nothing for integral operands, which Table 11-20 combines.
// `operand` is the first expression, whose type the result has.
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

static Logic4Vec EvalTernaryUnknownCond(const Expr* expr, SimContext& ctx,
                                        Arena& arena, uint32_t context_width) {
  auto tv = EvalExpr(expr->true_expr, ctx, arena, context_width);
  auto fv = EvalExpr(expr->false_expr, ctx, arena, context_width);
  // §11.4.11: for a real (nonintegral) result under an ambiguous condition, the
  // branches are compared for logical (numeric) equivalence. When equal the
  // shared value is returned; otherwise the result is the default value for the
  // resulting type (Table 7-1 gives 0.0 for real), not a bit-by-bit
  // combination.
  if (tv.is_real || fv.is_real) {
    double td = TernaryOperandToDouble(tv);
    double fd = TernaryOperandToDouble(fv);
    return MakeRealVec(arena, td == fd ? td : 0.0);
  }
  bool result_signed = tv.is_signed && fv.is_signed;
  uint32_t width = (tv.width > fv.width) ? tv.width : fv.width;
  if (context_width > width) width = context_width;
  if (tv.width < width) tv = ExtendVec(tv, width, result_signed, arena);
  if (fv.width < width) fv = ExtendVec(fv, width, result_signed, arena);
  // §11.4.11 returns either operand only where their logical equality
  // (§11.4.5) is 1 -- every bit known and equal -- so z bits the two share
  // still go through Table 11-20 and come out x.
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
  // Apply assignment-like context truncation (§10.8 conditional operands)
  if (context_width > 0 && result.width > context_width) {
    result = ResizeToWidth(result, context_width, arena);
  }
  return result;
}
// §11.4.11: when one conditional branch is real and the other is integral, the
// integral branch is cast to real. The result must carry the numeric VALUE of
// the integral operand encoded as a real bit pattern, not the raw integer bits
// (which a later ToDouble would misread as an already-real value).
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
// §12.6.3: a conditional whose predicate binds pattern identifiers. They are
// created in a scope that holds the predicate's later clauses and the
// consequent (EvalMatchesPredicate), and the alternative stands outside it.
// The operand not chosen names identifiers bound only when the predicate
// holds, so it is not read for the result type; the chosen one is extended
// by its own sign or truncated to the context.
static Logic4Vec EvalTernaryBindingPredicate(const Expr* expr, SimContext& ctx,
                                             Arena& arena,
                                             uint32_t context_width) {
  ctx.PushScope();
  bool holds = EvalMatchesPredicate(expr->condition, ctx, arena);
  Logic4Vec chosen;
  if (holds) chosen = EvalExpr(expr->true_expr, ctx, arena, context_width);
  ctx.PopScope();
  if (!holds) chosen = EvalExpr(expr->false_expr, ctx, arena, context_width);
  if (chosen.is_real || context_width == 0) return chosen;
  if (chosen.width < context_width)
    return ExtendVec(chosen, context_width, chosen.is_signed, arena);
  return ResizeToWidth(chosen, context_width, arena);
}

// §11.8.1 makes the conditional unsigned where either of its results is, and
// §11.8.2 propagates that type down to both, so `c ? -s : u` negates s
// zero-extended; a type propagated down to the conditional reaches them too.
Logic4Vec EvalTernary(const Expr* expr, SimContext& ctx, Arena& arena,
                      uint32_t context_width, bool unsigned_context) {
  if (PatternBindsIdentifiers(expr->condition))
    return EvalTernaryBindingPredicate(expr, ctx, arena, context_width);
  // §11.4.11 with §11.4.7: the predicate is read by its truth value, every
  // word of it and a real by its value, so a 128-bit predicate set at bit 100
  // is true and a real -0.0 false.
  const Truth kPredicate = TruthOf(EvalExpr(expr->condition, ctx, arena));
  if (kPredicate == Truth::kAmbiguous) {
    return EvalTernaryUnknownCond(expr, ctx, arena, context_width);
  }
  // §11.4.11: a determinate predicate evaluates the expression it chooses and
  // not the other, which §11.3.5 then lets neither take effect nor report. The
  // other still gives the result its type, read from its form (§11.6.1,
  // §11.8.1): as wide as the wider, signed where both are, real where either
  // is.
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
  // §11.4.11: a real branch forces a real result type; an integral chosen
  // branch is converted to its real value before being returned.
  if (kReal) {
    if (!chosen.is_real) chosen = IntegralToReal(chosen, arena);
    return chosen;
  }
  uint32_t width =
      std::max({chosen.width, SimSelfWidth(other_expr, ctx), context_width});
  Logic4Vec result = chosen.width < width
                         ? ExtendVec(chosen, width, chosen.is_signed, arena)
                         : chosen;
  // Apply assignment-like context truncation (§10.8 conditional operands)
  if (context_width > 0 && result.width > context_width) {
    result = ResizeToWidth(result, context_width, arena);
  }
  return result;
}

}  // namespace delta
