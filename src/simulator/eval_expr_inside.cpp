#include <cstddef>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

static uint64_t ResolveDollarBound(uint32_t width, bool lower) {
  if (lower) return 0;
  if (width >= 64) return ~uint64_t{0};
  return (uint64_t{1} << width) - 1;
}

static void ComputeToleranceBounds(uint64_t a, uint64_t b, TokenKind op,
                                   uint64_t& lo, uint64_t& hi) {
  uint64_t tol = b;
  if (op == TokenKind::kPlusPercentMinus) tol = a * b / 100;
  lo = (a >= tol) ? a - tol : 0;
  hi = a + tol;
  if (lo > hi) std::swap(lo, hi);
}

static int InsideMatchTolerance(uint64_t lv, const Expr* elem, SimContext& ctx,
                                Arena& arena) {
  auto a_v = EvalExpr(elem->index, ctx, arena);
  auto b_v = EvalExpr(elem->index_end, ctx, arena);
  if (!a_v.IsKnown() || !b_v.IsKnown()) return 2;
  uint64_t lo = 0;
  uint64_t hi = 0;
  ComputeToleranceBounds(a_v.ToUint64(), b_v.ToUint64(), elem->op, lo, hi);
  return (lv >= lo && lv <= hi) ? 1 : 0;
}

static bool IsDollarExpr(const Expr* e) {
  return e->kind == ExprKind::kIdentifier && e->text == "$";
}

static int InsideMatchRange(Logic4Vec lhs, const Expr* elem, SimContext& ctx,
                            Arena& arena) {
  if (elem->op == TokenKind::kPlusSlashMinus ||
      elem->op == TokenKind::kPlusPercentMinus) {
    if (!lhs.IsKnown()) return 2;
    return InsideMatchTolerance(lhs.ToUint64(), elem, ctx, arena);
  }

  uint64_t lo = IsDollarExpr(elem->index)
                    ? ResolveDollarBound(lhs.width, true)
                    : EvalExpr(elem->index, ctx, arena).ToUint64();
  uint64_t hi = IsDollarExpr(elem->index_end)
                    ? ResolveDollarBound(lhs.width, false)
                    : EvalExpr(elem->index_end, ctx, arena).ToUint64();
  if (lo > hi) return 0;

  // §11.4.13: with x/z bits in the left operand the comparison ranges over
  // every concretization of the unknown bits. ToUint64() projects those bits to
  // 0 (the minimum); setting them to 1 gives the maximum. If the whole span
  // lies inside [lo, hi] the membership is a definite 1; if it lies entirely
  // outside, a definite 0; otherwise the comparison is ambiguous (x) and
  // OR-reduces with the other set members.
  uint64_t unknown = lhs.nwords > 0 ? lhs.words[0].bval : 0;
  uint64_t lv_min = lhs.ToUint64();
  uint64_t lv_max = lv_min | unknown;
  if (lv_min >= lo && lv_max <= hi) return 1;
  if (lv_max < lo || lv_min > hi) return 0;
  return 2;
}

// Compares the left-hand expression against one singular set member, returning
// 1 for a match, 0 for a mismatch, and 2 when the comparison is ambiguous (x).
// Integral members use wildcard equality so an x or z bit on the member side is
// a do-not-care, while an x or z bit that survives on the left-hand side leaves
// the comparison ambiguous (§11.4.13, §11.4.6).
static int CompareInsideValue(const Logic4Vec& lhs, const Logic4Vec& ev) {
  uint64_t rhs_dc = ev.nwords > 0 ? ev.words[0].bval : 0;
  uint64_t lhs_x = lhs.nwords > 0 ? lhs.words[0].bval : 0;
  if (lhs_x & ~rhs_dc) return 2;
  if (rhs_dc || lhs_x) {
    return (((lhs.ToUint64() ^ ev.ToUint64()) & ~rhs_dc) == 0) ? 1 : 0;
  }
  return (lhs.ToUint64() == ev.ToUint64()) ? 1 : 0;
}

static int InsideMatchValue(Logic4Vec lhs, const Expr* elem, SimContext& ctx,
                            Arena& arena) {
  return CompareInsideValue(lhs, EvalExpr(elem, ctx, arena));
}

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
static bool CollectUnpackedSetMembers(const Expr* elem, SimContext& ctx,
                                      std::vector<Logic4Vec>& out) {
  if (elem->kind != ExprKind::kIdentifier) return false;
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
                                   const std::vector<Logic4Vec>& members) {
  int result = 0;
  for (const auto& member : members) {
    int mr = CompareInsideValue(lhs, member);
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
  out = MatchUnpackedSetMembers(lhs, members);
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

Logic4Vec EvalInside(const Expr* expr, SimContext& ctx, Arena& arena) {
  auto lhs = EvalExpr(expr->lhs, ctx, arena);
  bool ambiguous = false;
  for (auto* elem : expr->elements) {
    int r = EvalInsideElement(lhs, elem, ctx, arena);
    if (r == 1) return MakeLogic4VecVal(arena, 1, 1);
    if (r == 2) ambiguous = true;
  }
  if (ambiguous) {
    auto x = MakeLogic4Vec(arena, 1);
    x.words[0] = {~uint64_t{0}, ~uint64_t{0}};
    return x;
  }
  return MakeLogic4VecVal(arena, 1, 0);
}

}  // namespace delta
