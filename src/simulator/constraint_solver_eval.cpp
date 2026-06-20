#include <cstdint>
#include <unordered_set>
#include <vector>

#include "simulator/constraint_solver.h"
#include "simulator/constraint_solver_internal.h"

namespace delta {

static bool EvalRange(int64_t val, int64_t lo, int64_t hi) {
  return val >= lo && val <= hi;
}

static bool EvalSetMembership(int64_t val,
                              const std::vector<int64_t>& set_values) {
  for (int64_t v : set_values) {
    if (val == v) return true;
  }
  return false;
}

static bool EvalComparison(ConstraintKind kind, int64_t val, int64_t target) {
  switch (kind) {
    case ConstraintKind::kEqual:
      return val == target;
    case ConstraintKind::kNotEqual:
      return val != target;
    case ConstraintKind::kLessThan:
      return val < target;
    case ConstraintKind::kGreaterThan:
      return val > target;
    case ConstraintKind::kLessEqual:
      return val <= target;
    case ConstraintKind::kGreaterEqual:
      return val >= target;
    default:
      return true;
  }
}

bool ConstraintSolver::EvalConstraint(const ConstraintExpr& expr) const {
  switch (expr.kind) {
    case ConstraintKind::kRange: {
      auto it = values_.find(expr.var_name);
      if (it == values_.end()) return true;
      return EvalRange(it->second, expr.lo, expr.hi);
    }
    case ConstraintKind::kSetMembership: {
      auto it = values_.find(expr.var_name);
      if (it == values_.end()) return true;
      return EvalSetMembership(it->second, expr.set_values);
    }
    case ConstraintKind::kEqual:
    case ConstraintKind::kNotEqual:
    case ConstraintKind::kLessThan:
    case ConstraintKind::kGreaterThan:
    case ConstraintKind::kLessEqual:
    case ConstraintKind::kGreaterEqual: {
      auto it = values_.find(expr.var_name);
      if (it == values_.end()) return true;
      return EvalComparison(expr.kind, it->second, expr.lo);
    }
    case ConstraintKind::kImplication:
      return EvalImplication(expr);
    case ConstraintKind::kIfElse:
      return EvalIfElse(expr);
    case ConstraintKind::kForeach:
      return EvalForeach(expr);
    case ConstraintKind::kArrayReduction:
      return EvalArrayReduction(expr);
    case ConstraintKind::kUnique:
      return EvalUnique(expr);
    case ConstraintKind::kDist:
    case ConstraintKind::kSoft:
    // 18.5.13.2: a 'disable soft' directive imposes no relation; it only
    // discards other soft constraints, so it is satisfied by any assignment.
    case ConstraintKind::kDisableSoft:

      return true;
    case ConstraintKind::kCustom:
      return expr.eval_fn ? expr.eval_fn(values_) : true;
  }
  return true;
}

bool ConstraintSolver::ApplyConstraint(const ConstraintExpr& expr) {
  if (expr.kind == ConstraintKind::kDist) {
    values_[expr.var_name] = SampleDist(expr);
    return true;
  }
  return EvalConstraint(expr);
}

void CollectConstraints(const std::vector<ConstraintBlock>& blocks,
                        const std::vector<ConstraintExpr>& extra,
                        std::vector<const ConstraintExpr*>& hard,
                        std::vector<const ConstraintExpr*>& soft) {
  // 18.5.13.2: a 'disable soft' directive is neither a hard relation to satisfy
  // nor a soft preference to honor; it is resolved separately (see
  // ComputeDisabledSoft), so it is omitted from both lists here.
  auto classify = [&](const ConstraintExpr& c) {
    if (c.kind == ConstraintKind::kDisableSoft) return;
    if (c.kind == ConstraintKind::kSoft) {
      soft.push_back(&c);
    } else {
      hard.push_back(&c);
    }
  };
  for (const auto& block : blocks) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) classify(c);
  }
  for (const auto& c : extra) classify(c);
}

bool ConstraintSolver::CheckAllConstraints(
    const std::vector<ConstraintExpr>& extra, bool include_soft) {
  std::vector<const ConstraintExpr*> hard;
  std::vector<const ConstraintExpr*> soft;
  CollectConstraints(blocks_, extra, hard, soft);
  for (const auto* c : hard) {
    if (c->has_guard) {
      // 18.5.12: evaluate the guard before imposing the guarded constraint.
      // The guard prevents the solver from generating evaluation errors on the
      // guarded set, sifting away subexpressions that would otherwise error.
      switch (GuardFinalOutcome(EvaluateGuard(c->guard, values_))) {
        case GuardOutcome::kError:
          // An ERROR guard generates an unconditional error; the constraint
          // fails and no resampling can recover it.
          guard_error_ = true;
          return false;
        case GuardOutcome::kEliminated:
          // A FALSE guard eliminates the constraint and generates no error.
          continue;
        case GuardOutcome::kUnconditional:
        case GuardOutcome::kConditional:
          // A TRUE or RANDOM guard lets the guarded constraint be generated.
          break;
      }
    }
    if (!EvalConstraint(*c)) return false;
  }
  if (include_soft) {
    // 18.5.13: while the soft constraints are still active, the solver attempts
    // to satisfy them together with the hard constraints. A soft constraint is
    // an inner expression_or_dist preceded by soft; enforce that inner relation
    // here so a candidate assignment must honor it. When this set proves
    // jointly unsatisfiable the caller drops the soft constraints and retries
    // with include_soft clear.
    for (const auto* c : soft) {
      // 18.5.13.1 / 18.5.13.2: a soft constraint discarded by the priority
      // resolution, or by a 'disable soft' directive, is treated as true, so
      // its inner relation imposes nothing.
      if (dropped_soft_.count(c) || disabled_soft_.count(c)) continue;
      const ConstraintExpr* inner = c->inner ? c->inner : nullptr;
      if (inner && !EvalConstraint(*inner)) return false;
    }
  }
  return true;
}

bool ConstraintSolver::EvalImplication(const ConstraintExpr& expr) const {
  // 18.5.5: a -> b is Boolean-equivalent to (!a || b). Evaluate the antecedent
  // a; when it does not hold the implication imposes nothing, so the consequent
  // variables are left unconstrained. When a holds, every constraint in the
  // consequent b must be satisfied. Because the solver only accepts an
  // assignment for which the whole expression evaluates true, the converse is
  // enforced as well: if b cannot be satisfied, a must come out false.
  bool antecedent;
  if (expr.cond_fn) {
    // The antecedent is an arbitrary integral/real expression.
    antecedent = expr.cond_fn(values_);
  } else {
    // Short form: the antecedent is the equality cond_var == cond_value.
    auto it = values_.find(expr.cond_var);
    if (it == values_.end()) return true;
    antecedent = (it->second == expr.cond_value);
  }
  if (!antecedent) return true;
  for (const auto& sub : expr.sub_constraints) {
    if (!EvalConstraint(sub)) return false;
  }
  return true;
}

bool ConstraintSolver::EvalIfElse(const ConstraintExpr& expr) const {
  // 18.5.6: "if (cond) then_set else else_set" is equivalent to the implication
  // pair cond -> then_set and !cond -> else_set. When the condition is true,
  // every constraint in the then set must be satisfied; otherwise every
  // constraint in the optional else set must be satisfied (an absent else set
  // imposes nothing). The condition and the guarded sets are interdependent:
  // because the solver only accepts an assignment for which the whole
  // expression evaluates true, the chosen branch also constrains the condition.
  bool cond;
  if (expr.cond_fn) {
    // The condition is an arbitrary integral or real expression.
    cond = expr.cond_fn(values_);
  } else {
    // Short form: the condition is the equality cond_var == cond_value.
    auto it = values_.find(expr.cond_var);
    if (it == values_.end()) return true;
    cond = (it->second == expr.cond_value);
  }
  const auto& branch = cond ? expr.sub_constraints : expr.else_constraints;
  for (const auto& sub : branch) {
    if (!EvalConstraint(sub)) return false;
  }
  return true;
}

bool ConstraintSolver::EvalForeach(const ConstraintExpr& expr) const {
  // 18.5.7.1: a foreach iterative constraint applies its constraint_set to the
  // elements of the array. When the array is dynamically sized, its size method
  // is a state variable within the foreach block: the size constraints are
  // solved first, so the solver reads the size value already committed and
  // imposes the per-element constraints only on the elements that exist, i.e.
  // those whose index is below that size. A foreach over a fixed-size array
  // leaves size_var empty, in which case every per-element constraint applies.
  size_t count = expr.sub_constraints.size();
  if (!expr.size_var.empty()) {
    auto it = values_.find(expr.size_var);
    if (it != values_.end()) {
      int64_t sz = it->second < 0 ? 0 : it->second;
      if (static_cast<size_t>(sz) < count) count = static_cast<size_t>(sz);
    }
  }
  for (size_t i = 0; i < count; ++i) {
    if (!EvalConstraint(expr.sub_constraints[i])) return false;
  }
  return true;
}

bool ConstraintSolver::EvalArrayReduction(const ConstraintExpr& expr) const {
  // 18.5.7.2: an array reduction method in a constraint is treated as an
  // expression iterated over each element of the array, joined by the relevant
  // operand for the method. Begin from the operand's identity so a fold over
  // any number of elements is well defined, then combine each element in turn.
  int64_t acc = 0;
  switch (expr.reduce_op) {
    case ArrayReductionOp::kSum:
    case ArrayReductionOp::kOr:
    case ArrayReductionOp::kXor:
      acc = 0;
      break;
    case ArrayReductionOp::kProduct:
      acc = 1;
      break;
    case ArrayReductionOp::kAnd:
      acc = -1;  // all ones: the identity of bitwise AND
      break;
  }

  // As with a foreach iterative constraint, an array's size method is a state
  // variable here: the size constraints are solved first, so only the elements
  // whose index is below the committed size participate in the reduction. A
  // fixed-size array leaves size_var empty, so every named element is folded.
  size_t count = expr.reduce_vars.size();
  if (!expr.size_var.empty()) {
    auto sit = values_.find(expr.size_var);
    if (sit != values_.end()) {
      int64_t sz = sit->second < 0 ? 0 : sit->second;
      if (static_cast<size_t>(sz) < count) count = static_cast<size_t>(sz);
    }
  }

  for (size_t i = 0; i < count; ++i) {
    auto it = values_.find(expr.reduce_vars[i]);
    if (it == values_.end()) continue;
    // The with-clause expression maps each element value (the 'item') to the
    // value folded into the reduction; absent a with clause the element value
    // itself is folded.
    int64_t v = expr.reduce_with ? expr.reduce_with(it->second) : it->second;
    switch (expr.reduce_op) {
      case ArrayReductionOp::kSum:
        acc += v;
        break;
      case ArrayReductionOp::kProduct:
        acc *= v;
        break;
      case ArrayReductionOp::kAnd:
        acc &= v;
        break;
      case ArrayReductionOp::kOr:
        acc |= v;
        break;
      case ArrayReductionOp::kXor:
        acc ^= v;
        break;
    }
  }

  // 18.5.7.2: the reduction returns a single value of the array element type,
  // or the type of the with-clause expression when one is specified. Truncate
  // the fold to that result type's width so a sum that would overflow the
  // element type wraps, while a wider with-clause type (e.g. int'(item))
  // preserves it.
  if (expr.reduce_width > 0 && expr.reduce_width < 64) {
    uint64_t mask = (static_cast<uint64_t>(1) << expr.reduce_width) - 1;
    acc = static_cast<int64_t>(static_cast<uint64_t>(acc) & mask);
  }

  return EvalComparison(expr.reduce_cmp, acc, expr.lo);
}

bool ConstraintSolver::EvalUnique(const ConstraintExpr& expr) const {
  std::unordered_set<int64_t> seen;
  for (const auto& vname : expr.unique_vars) {
    auto it = values_.find(vname);
    if (it == values_.end()) continue;
    if (seen.count(it->second)) return false;
    seen.insert(it->second);
  }
  return true;
}

}  // namespace delta
