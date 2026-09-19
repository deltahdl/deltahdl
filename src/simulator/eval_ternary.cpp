#include <algorithm>
#include <cstdint>
#include <cstring>

#include "common/arena.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"
#include "simulator/evaluation_internal.h"
#include "simulator/statement_assign.h"

namespace delta {

// §11.4.11: the conditional operator. A determinate condition selects one
// operand and leaves the other unevaluated where it could mutate state; an
// ambiguous one combines the two bit by bit, or compares them numerically
// where either is real.

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
// §11.4.11: the unselected conditional operand shall not be evaluated. An
// operand that could mutate state (an embedded assignment, ++/--, or a call)
// is detected here so the determinate-condition path can skip it; a pure
// operand is still evaluated to recover its result-type metadata.
static bool ExprNodeIsSideEffect(const Expr* e) {
  if (e->kind == ExprKind::kCall || e->kind == ExprKind::kSystemCall)
    return true;
  if (e->kind == ExprKind::kBinary &&
      (e->op == TokenKind::kEq || IsCompoundAssignOp(e->op)))
    return true;
  return (e->kind == ExprKind::kUnary || e->kind == ExprKind::kPostfixUnary) &&
         (e->op == TokenKind::kPlusPlus || e->op == TokenKind::kMinusMinus);
}
static bool ExprMayHaveSideEffect(const Expr* e) {
  if (e == nullptr) return false;
  if (ExprNodeIsSideEffect(e)) return true;
  const Expr* children[] = {e->lhs,  e->rhs,   e->condition,  e->true_expr,
                            e->base, e->index, e->false_expr, e->index_end};
  for (const auto* c : children)
    if (ExprMayHaveSideEffect(c)) return true;
  for (const auto* a : e->args)
    if (ExprMayHaveSideEffect(a)) return true;
  for (const auto* el : e->elements)
    if (ExprMayHaveSideEffect(el)) return true;
  return false;
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
  Logic4Vec result;
  if (EvalCaseEquality(tv, fv)) {
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
// §11.4.11: the self-determined result type of a conditional operator -- the
// two branches together decide signedness, realness, and width.
struct TernaryResultType {
  bool is_signed;
  bool is_real;
  uint32_t width;
};

// Fold the unselected branch's own type into the result type: the result is
// signed only when both branches are, as wide as the wider branch, and real
// when either branch is.
static void WidenTernaryResultType(const Logic4Vec& other,
                                   TernaryResultType& rt) {
  rt.is_signed = rt.is_signed && other.is_signed;
  if (other.width > rt.width) rt.width = other.width;
  if (other.is_real) rt.is_real = true;
}

Logic4Vec EvalTernary(const Expr* expr, SimContext& ctx, Arena& arena,
                      uint32_t context_width) {
  auto cond = EvalExpr(expr->condition, ctx, arena);

  if (HasUnknownBits(cond)) {
    return EvalTernaryUnknownCond(expr, ctx, arena, context_width);
  }
  // §11.4.11: a determinate condition selects exactly one expression; the
  // other shall not be evaluated. A side-effect-free unselected expression is
  // still evaluated so its width/signedness/realness contribute to the result
  // type, but one that could mutate state is skipped.
  bool cond_true = cond.ToUint64() != 0;
  const Expr* other_expr = cond_true ? expr->false_expr : expr->true_expr;
  auto chosen = EvalExpr(cond_true ? expr->true_expr : expr->false_expr, ctx,
                         arena, context_width);
  TernaryResultType rt{chosen.is_signed, chosen.is_real, chosen.width};
  if (!ExprMayHaveSideEffect(other_expr))
    WidenTernaryResultType(EvalExpr(other_expr, ctx, arena, context_width), rt);
  // §11.4.11: a real branch forces a real result type; an integral chosen
  // branch is converted to its real value before being returned.
  if (rt.is_real) {
    if (!chosen.is_real) chosen = IntegralToReal(chosen, arena);
    return chosen;
  }
  uint32_t width = std::max(rt.width, context_width);
  Logic4Vec result = chosen.width < width
                         ? ExtendVec(chosen, width, rt.is_signed, arena)
                         : chosen;
  result.is_signed = rt.is_signed;
  // Apply assignment-like context truncation (§10.8 conditional operands)
  if (context_width > 0 && result.width > context_width) {
    result = ResizeToWidth(result, context_width, arena);
  }
  return result;
}

}  // namespace delta
