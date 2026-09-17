#include <cstdint>
#include <string>

#include "parser/ast.h"
#include "simulator/constraint_solver.h"
#include "simulator/eval_randomize_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

namespace {

// 18.5.3: a bound of a distribution item, read both as the integer an integral
// variable's distribution takes it for and as the real a real variable's does.
// 6.11.3: a signed operand holding a negative number is read as the type it
// was written in, so the clause's ZSTATE of -100 is -100 rather than a large
// positive.
struct DistBound {
  int64_t integral = 0;
  double real = 0.0;
};

DistBound EvalDistBound(const Expr* e, RandomizeCtx& rc) {
  auto cv = EvalExpr(e, rc.ctx, rc.arena);
  DistBound b;
  if (cv.is_real) {
    b.real = RealVecToDouble(cv);
    b.integral = static_cast<int64_t>(b.real);
    return b;
  }
  b.integral = cv.is_signed ? SignExtend(cv.ToUint64(), cv.width)
                            : static_cast<int64_t>(cv.ToUint64());
  b.real = static_cast<double>(b.integral);
  return b;
}

// 11.4.13: the ends of a value_range written about a centre, '[centre +/-
// tol]' spanning tol either side of it and '[centre +%- tol]' spanning tol
// percent of it, the clause's [VALUE_NOM +%- 1.0] being 3.3 give or take
// 0.033.
void ToleranceEnds(const DistBound& centre, const DistBound& tol, bool relative,
                   DistWeight& w) {
  double half = relative ? centre.real * tol.real / 100.0 : tol.real;
  if (half < 0) half = -half;
  w.real_lo = centre.real - half;
  w.real_hi = centre.real + half;
  int64_t ihalf =
      relative ? centre.integral * tol.integral / 100 : tol.integral;
  if (ihalf < 0) ihalf = -ihalf;
  w.lo = centre.integral - ihalf;
  w.hi = centre.integral + ihalf;
}

}  // namespace

// 18.5.3: translate a captured "expression dist { dist_list }" into a kDist
// solver constraint. The distribution names the single variable it weights, so
// the target must be a plain identifier; each item's value/range bounds and its
// weight are constant expressions, folded here both to the integers an
// integral variable is drawn from and to the reals a real one is, the solver
// reading whichever its variable takes. A range keeps its per_element flag so
// the solver spreads a ':=' weight across the range, and an item with no
// explicit weight keeps the DistWeight default weight of 1. Returns false for a
// non-identifier target, leaving the distribution unbuilt.
bool BuildDistConstraint(const ConstraintDistRef& ref, RandomizeCtx& rc,
                         ConstraintExpr& out) {
  if (ref.target == nullptr || ref.target->kind != ExprKind::kIdentifier)
    return false;
  out.kind = ConstraintKind::kDist;
  out.var_name = std::string(ref.target->text);
  ConstraintEvalScope scope(rc.obj, rc.ctx);
  for (const auto& item : ref.items) {
    DistWeight w;
    w.is_default = item.is_default;
    w.is_range = item.is_range;
    w.per_element = item.per_element;
    if (item.weight != nullptr)
      w.weight = static_cast<uint32_t>(
          EvalExpr(item.weight, rc.ctx, rc.arena).ToUint64());
    if (item.is_range && item.tolerance != nullptr) {
      ToleranceEnds(EvalDistBound(item.lo, rc),
                    EvalDistBound(item.tolerance, rc), item.tolerance_relative,
                    w);
    } else if (item.is_range) {
      DistBound lo = EvalDistBound(item.lo, rc);
      DistBound hi = EvalDistBound(item.hi, rc);
      w.lo = lo.integral;
      w.hi = hi.integral;
      w.real_lo = lo.real;
      w.real_hi = hi.real;
    } else if (!item.is_default) {
      DistBound value = EvalDistBound(item.value, rc);
      w.value = value.integral;
      w.real_value = value.real;
    }
    out.dist_weights.push_back(w);
  }
  return true;
}

}  // namespace delta
