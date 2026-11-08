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

int ComparisonOutcome(const Logic4Vec& bit) {
  if (!bit.IsKnown()) return 2;
  return bit.ToUint64() != 0 ? 1 : 0;
}

Logic4Vec Compare(TokenKind op, Logic4Vec lhs, Logic4Vec rhs, Arena& arena) {
  if (!lhs.is_real && !rhs.is_real && !lhs.is_string && !rhs.is_string) {
    const uint32_t kWidth = std::max(lhs.width, rhs.width);
    const bool kSigned = lhs.is_signed && rhs.is_signed;
    if (lhs.width < kWidth) lhs = ExtendVec(lhs, kWidth, kSigned, arena);
    if (rhs.width < kWidth) rhs = ExtendVec(rhs, kWidth, kSigned, arena);
  }
  return EvalBinaryOp(op, lhs, rhs, arena, 0);
}

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

double RealOf(const Logic4Vec& v) {
  if (v.is_real) return RealVecToDouble(v);
  if (v.is_signed) return static_cast<double>(LongintValue(v));
  return static_cast<double>(v.ToUint64());
}

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

bool CollectUnpackedSetMembers(const Expr* elem, SimContext& ctx,
                               std::vector<Logic4Vec>& out) {
  if (elem->kind != ExprKind::kIdentifier) return false;
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

static bool TryMatchUnpackedSetMember(const Logic4Vec& lhs, const Expr* elem,
                                      SimContext& ctx, int& out) {
  std::vector<Logic4Vec> members;
  if (!CollectUnpackedSetMembers(elem, ctx, members)) return false;
  out = MatchUnpackedSetMembers(lhs, members, ctx.GetArena());
  return true;
}

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
