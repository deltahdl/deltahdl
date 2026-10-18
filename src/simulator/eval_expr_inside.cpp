#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "simulator/eval_array.h"
#include "simulator/eval_class_array.h"
#include "simulator/evaluation.h"
#include "simulator/evaluation_internal.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

namespace {

// The 1, 0 or x a one-bit comparison gives, as EvalInsideElement's 1, 0 and 2.
int ComparisonOutcome(const Logic4Vec& bit) {
  if (!bit.IsKnown()) return 2;
  return bit.ToUint64() != 0 ? 1 : 0;
}

// §11.6.1 with §11.8.1: a comparison of two integral operands sizes both to
// the larger of their widths, extending by sign where both are signed; a real
// or a string operand is compared as it stands.
Logic4Vec Compare(TokenKind op, Logic4Vec lhs, Logic4Vec rhs, Arena& arena) {
  if (!lhs.is_real && !rhs.is_real && !lhs.is_string && !rhs.is_string) {
    const uint32_t kWidth = std::max(lhs.width, rhs.width);
    const bool kSigned = lhs.is_signed && rhs.is_signed;
    if (lhs.width < kWidth) lhs = ExtendVec(lhs, kWidth, kSigned, arena);
    if (rhs.width < kWidth) rhs = ExtendVec(rhs, kWidth, kSigned, arena);
  }
  return EvalBinaryOp(op, lhs, rhs, arena, 0);
}

// §11.4.13: whether `lhs` is inclusively within [lo:hi], by `>=` and `<=` on
// their own types. A range whose low bound is above its high one is empty.
int WithinRange(const Logic4Vec& lhs, const Logic4Vec& lo, const Logic4Vec& hi,
                Arena& arena) {
  if (ComparisonOutcome(Compare(TokenKind::kGt, lo, hi, arena)) == 1) return 0;
  const int kAbove =
      ComparisonOutcome(Compare(TokenKind::kGtEq, lhs, lo, arena));
  const int kBelow =
      ComparisonOutcome(Compare(TokenKind::kLtEq, lhs, hi, arena));
  if (kAbove == 0 || kBelow == 0) return 0;
  return kAbove == 1 && kBelow == 1 ? 1 : 2;
}

// The real value of `v`, a real one as it is and an integral one by its sign.
double RealOf(const Logic4Vec& v) {
  if (v.is_real) return RealVecToDouble(v);
  if (v.is_signed) return static_cast<double>(LongintValue(v));
  return static_cast<double>(v.ToUint64());
}

// §11.4.13: a `$` bound stands for the lowest or the highest value of the left
// operand's type -- the extremes of a real, the sign bit alone and every bit
// but it for a signed integral type, and no bit and every bit for an unsigned
// one.
Logic4Vec DollarBound(const Logic4Vec& lhs, bool lower, Arena& arena) {
  if (lhs.is_real) {
    const double kMax = std::numeric_limits<double>::max();
    return MakeRealVec(arena, lower ? -kMax : kMax, lhs.width);
  }
  Logic4Vec bound = MakeLogic4Vec(arena, lhs.width);
  for (uint32_t b = 0; b < lhs.width; ++b) {
    const bool kIsSignBit = lhs.is_signed && b == lhs.width - 1;
    if (lower == kIsSignBit)
      bound.words[b / 64].aval |= uint64_t{1} << (b % 64);
  }
  bound.is_signed = lhs.is_signed;
  return bound;
}

// §11.4.13: [A +/- B] is [A-type(A)'(B) : A+type(A)'(B)] and [A +%- B] is
// [A-type(A)'(A*B/100.0) : A+type(A)'(A*B/100.0)], the bounds ordered
// whatever their signs and of A's type, a tolerance converted to an integral
// A truncated rather than rounded: 25% of 7 is [6:8] and of -7 is [-8:-6].
int InsideMatchTolerance(const Logic4Vec& lhs, const Expr* elem,
                         SimContext& ctx, Arena& arena) {
  auto a_v = EvalExpr(elem->index, ctx, arena);
  auto b_v = EvalExpr(elem->index_end, ctx, arena);
  if (!a_v.IsKnown() || !b_v.IsKnown()) return 2;
  const double kA = RealOf(a_v);
  double tolerance = RealOf(b_v);
  if (elem->op == TokenKind::kPlusPercentMinus)
    tolerance = kA * tolerance / 100.0;
  if (a_v.is_real) {
    const double kLo = std::min(kA - tolerance, kA + tolerance);
    const double kHi = std::max(kA - tolerance, kA + tolerance);
    return WithinRange(lhs, MakeRealVec(arena, kLo, a_v.width),
                       MakeRealVec(arena, kHi, a_v.width), arena);
  }
  const auto kTolerance = static_cast<int64_t>(tolerance);
  const int64_t kInt = LongintValue(a_v);
  const int64_t kLo = std::min(kInt - kTolerance, kInt + kTolerance);
  const int64_t kHi = std::max(kInt - kTolerance, kInt + kTolerance);
  Logic4Vec lo = MakeLogic4VecVal(arena, a_v.width, static_cast<uint64_t>(kLo));
  Logic4Vec hi = MakeLogic4VecVal(arena, a_v.width, static_cast<uint64_t>(kHi));
  lo.is_signed = a_v.is_signed;
  hi.is_signed = a_v.is_signed;
  return WithinRange(lhs, lo, hi, arena);
}

bool IsDollarExpr(const Expr* e) {
  return e->kind == ExprKind::kIdentifier && e->text == "$";
}

// §11.4.13: a range is matched by `<=` and `>=`, so an x or z bit in the left
// operand leaves the comparison ambiguous, which the OR reduction over the set
// keeps unless another member matches.
int InsideMatchRange(const Logic4Vec& lhs, const Expr* elem, SimContext& ctx,
                     Arena& arena) {
  if (elem->op == TokenKind::kPlusSlashMinus ||
      elem->op == TokenKind::kPlusPercentMinus)
    return InsideMatchTolerance(lhs, elem, ctx, arena);
  Logic4Vec lo = IsDollarExpr(elem->index) ? DollarBound(lhs, true, arena)
                                           : EvalExpr(elem->index, ctx, arena);
  Logic4Vec hi = IsDollarExpr(elem->index_end)
                     ? DollarBound(lhs, false, arena)
                     : EvalExpr(elem->index_end, ctx, arena);
  return WithinRange(lhs, lo, hi, arena);
}

// §11.4.13 with §11.4.6: an integral set member is compared by wildcard
// equality, so its x and z bits are do-not-cares and the left operand's are
// not, and a nonintegral one -- a real, a string -- by equality, each on the
// operands' own widths, signedness and every word.
int CompareInsideValue(const Logic4Vec& lhs, const Logic4Vec& ev,
                       Arena& arena) {
  const bool kIntegral =
      !lhs.is_real && !ev.is_real && !lhs.is_string && !ev.is_string;
  return ComparisonOutcome(Compare(
      kIntegral ? TokenKind::kEqEqQuestion : TokenKind::kEqEq, lhs, ev, arena));
}

int InsideMatchValue(const Logic4Vec& lhs, const Expr* elem, SimContext& ctx,
                     Arena& arena) {
  return CompareInsideValue(lhs, EvalExpr(elem, ctx, arena), arena);
}

}  // namespace

// §11.4.13: descends every unpacked dimension of a multidimensional array set
// member, gathering the singular per-element leaf values named arr[i0][i1]...
// in row-major order (matching how lowerer_var.cpp materialized them). A
// missing leaf contributes a default value of the element width so the count of
// scanned members is preserved.
static void CollectMultiDimSetLeaves(const ArrayInfo& info, size_t d,
                                     const std::string& prefix, SimContext& ctx,
                                     std::vector<Logic4Vec>& out) {
  if (d == info.dim_sizes.size()) {
    auto* var = ctx.FindVariable(prefix);
    out.push_back(var ? var->value
                      : MakeLogic4Vec(ctx.GetArena(), info.elem_width));
    return;
  }
  uint32_t lo = info.dim_los[d];
  for (uint32_t i = 0; i < info.dim_sizes[d]; ++i) {
    CollectMultiDimSetLeaves(
        info, d + 1, prefix + "[" + std::to_string(lo + i) + "]", ctx, out);
  }
}

// §11.4.13: a set member that names an unpacked array is not compared as an
// aggregate. Instead its elements are traversed down to singular values, so the
// membership test sees each element as if it had been listed individually.
// Returns true (filling `out`) when `elem` named an unpacked array, covering
// queues/dynamic arrays, associative arrays in index order, single-dimension
// fixed arrays, and (by full descent through every dimension) multidimensional
// fixed arrays. An associative array contributed no value, so `3 inside {m}`
// with m["a"] = 3 answered 0.
bool CollectUnpackedSetMembers(const Expr* elem, SimContext& ctx,
                               std::vector<Logic4Vec>& out) {
  if (elem->kind != ExprKind::kIdentifier) return false;
  // §8.5 with §7.6: an array property of the object in scope, which hides a
  // like-named array of the enclosing module.
  if (PropertyArrayElements(elem, ctx, ctx.GetArena(), out)) return true;
  if (CollectQueueOrAssocValues(elem->text, ctx, out)) return true;
  if (auto* info = ctx.FindArrayInfo(elem->text)) {
    if (info->dim_sizes.size() >= 2) {
      CollectMultiDimSetLeaves(*info, 0, std::string(elem->text), ctx, out);
      return true;
    }
    for (uint32_t i = 0; i < info->size; ++i) {
      std::string elem_name =
          std::string(elem->text) + "[" + std::to_string(info->lo + i) + "]";
      auto* var = ctx.FindVariable(elem_name);
      out.push_back(var ? var->value
                        : MakeLogic4Vec(ctx.GetArena(), info->elem_width));
    }
    return true;
  }
  return false;
}

// Tests `lhs` against each singular value collected from an unpacked-array set
// member. Returns 1 on the first match, 2 if any comparison was ambiguous (and
// none matched), and 0 otherwise.
static int MatchUnpackedSetMembers(const Logic4Vec& lhs,
                                   const std::vector<Logic4Vec>& members,
                                   Arena& arena) {
  int result = 0;
  for (const auto& member : members) {
    int mr = CompareInsideValue(lhs, member, arena);
    if (mr == 1) return 1;
    if (mr == 2) result = 2;
  }
  return result;
}

// When `elem` (in a non-range position) names an unpacked array, traverses it
// to singular values per §11.4.13 and reports the membership result through
// `out`/the return value. Returns true when `elem` was such an array.
static bool TryMatchUnpackedSetMember(const Logic4Vec& lhs, const Expr* elem,
                                      SimContext& ctx, int& out) {
  std::vector<Logic4Vec> members;
  if (!CollectUnpackedSetMembers(elem, ctx, members)) return false;
  out = MatchUnpackedSetMembers(lhs, members, ctx.GetArena());
  return true;
}

// Evaluates `lhs inside { elem }` for one set member. Returns 1 on a match, 0
// on a definite mismatch, and 2 when the comparison was ambiguous (x). Handles
// ranges, unpacked-array members (traversed to singular values per §11.4.13),
// and plain singular values.
int EvalInsideElement(const Logic4Vec& lhs, const Expr* elem, SimContext& ctx,
                      Arena& arena) {
  bool is_range =
      elem->kind == ExprKind::kSelect && elem->index && elem->index_end;
  if (!is_range) {
    int unpacked_result = 0;
    if (TryMatchUnpackedSetMember(lhs, elem, ctx, unpacked_result)) {
      return unpacked_result;
    }
  }
  return is_range ? InsideMatchRange(lhs, elem, ctx, arena)
                  : InsideMatchValue(lhs, elem, ctx, arena);
}

// §16.14.2 with §18.5.3: whether `expr` is an assertion's dist whose list
// writes a default item, which stands for every value the other items leave
// out, so that the set the inside reading tests holds every value.
static bool DistHasDefaultItem(const Expr* expr) {
  if (expr->dist_items == nullptr) return false;
  return std::any_of(
      expr->dist_items->begin(), expr->dist_items->end(),
      [](const ConstraintDistItem& item) { return item.is_default; });
}

Logic4Vec EvalInside(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto lhs = EvalExpr(expr->lhs, ctx, arena);
  bool ambiguous = false;
  for (auto* elem : expr->elements) {
    int r = EvalInsideElement(lhs, elem, ctx, arena);
    if (r == 1) return MakeLogic4VecVal(arena, 1, 1);
    if (r == 2) ambiguous = true;
  }
  if (DistHasDefaultItem(expr)) return MakeLogic4VecVal(arena, 1, 1);
  if (ambiguous) {
    auto x = MakeLogic4Vec(arena, 1);
    x.words[0] = {~uint64_t{0}, ~uint64_t{0}};
    return x;
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

}  // namespace delta
