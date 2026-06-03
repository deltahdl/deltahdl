#include "simulator/constraint_solver.h"

#include <algorithm>
#include <cstdint>
#include <numeric>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

namespace delta {

ConstraintSolver::ConstraintSolver(uint32_t seed) : rng_(seed) {}

void ConstraintSolver::AddVariable(const RandVariable& var) {
  variables_[var.name] = var;
}

void ConstraintSolver::AddConstraintBlock(const ConstraintBlock& block) {
  blocks_.push_back(block);
}

void ConstraintSolver::SetRandMode(std::string_view name, bool enabled) {
  auto it = variables_.find(std::string(name));
  if (it != variables_.end()) it->second.enabled = enabled;
}

bool ConstraintSolver::GetRandMode(std::string_view name) const {
  auto it = variables_.find(std::string(name));
  return (it != variables_.end()) ? it->second.enabled : false;
}

void ConstraintSolver::SetAllRandMode(bool enabled) {
  for (auto& [name, var] : variables_) var.enabled = enabled;
}

void ConstraintSolver::ApplyInlineRandomList(
    const std::vector<std::string>& names) {
  // 18.11: the argument list designates the complete set of active random
  // variables; everything else becomes a state variable. Only the active flag
  // is touched here — the qualifier (and thus the cyclical mode) is left as it
  // was declared, so this can neither promote a variable to randc nor demote a
  // randc variable to noncyclical rand.
  std::unordered_set<std::string> active(names.begin(), names.end());
  for (auto& [name, var] : variables_) {
    var.enabled = active.find(name) != active.end();
  }
}

void ConstraintSolver::SetValue(std::string_view name, int64_t value) {
  auto it = variables_.find(std::string(name));
  if (it != variables_.end()) it->second.value = value;
}

void ConstraintSolver::SetConstraintMode(std::string_view block_name,
                                         bool enabled) {
  for (auto& block : blocks_) {
    if (block.name == block_name) block.enabled = enabled;
  }
}

bool ConstraintSolver::GetConstraintMode(std::string_view block_name) const {
  for (const auto& block : blocks_) {
    if (block.name == block_name) return block.enabled;
  }
  return false;
}

void ConstraintSolver::SetPreRandomize(RandomizeCallback cb) {
  pre_randomize_ = std::move(cb);
}

void ConstraintSolver::SetPostRandomize(RandomizeCallback cb) {
  post_randomize_ = std::move(cb);
}

const std::unordered_map<std::string, int64_t>& ConstraintSolver::GetValues()
    const {
  return values_;
}

int64_t ConstraintSolver::GenerateRandValue(RandVariable& var) {
  // 18.4.2: a static randc variable shares one cyclic permutation across every
  // instance of the class, so its history lives in the shared state when one is
  // attached; a nonstatic randc keeps its own per-instance history. Bind the
  // active history once here and advance it below, so the same draw-and-reject
  // logic serves both cases.
  std::unordered_set<int64_t>& history =
      (var.is_static && var.shared_randc_state) ? *var.shared_randc_state
                                                : var.randc_history;
  // 18.3: a random variable of enum type must take one of the enum's named
  // constants. The 18.4 exception (an enum member of a packed struct/union)
  // clears apply_enum_restriction, in which case the named set is ignored and
  // the value is drawn from the full declared range below.
  if (!var.enum_values.empty() && var.apply_enum_restriction) {
    if (var.qualifier == RandQualifier::kRandc) {
      if (history.size() >= var.enum_values.size()) {
        history.clear();
      }
      for (int attempt = 0; attempt < 1000; ++attempt) {
        std::uniform_int_distribution<size_t> pick(0, var.enum_values.size() - 1);
        int64_t val = var.enum_values[pick(rng_)];
        if (history.find(val) == history.end()) {
          history.insert(val);
          return val;
        }
      }
      for (int64_t v : var.enum_values) {
        if (history.find(v) == history.end()) {
          history.insert(v);
          return v;
        }
      }
      history.clear();
      history.insert(var.enum_values.front());
      return var.enum_values.front();
    }
    std::uniform_int_distribution<size_t> pick(0, var.enum_values.size() - 1);
    return var.enum_values[pick(rng_)];
  }
  if (var.qualifier == RandQualifier::kRandc) {
    int64_t range_size = var.max_val - var.min_val + 1;

    if (static_cast<int64_t>(history.size()) >= range_size) {
      history.clear();
    }

    for (int attempt = 0; attempt < 1000; ++attempt) {
      std::uniform_int_distribution<int64_t> dist(var.min_val, var.max_val);
      int64_t val = dist(rng_);
      if (history.find(val) == history.end()) {
        history.insert(val);
        return val;
      }
    }

    for (int64_t v = var.min_val; v <= var.max_val; ++v) {
      if (history.find(v) == history.end()) {
        history.insert(v);
        return v;
      }
    }
    history.clear();
    history.insert(var.min_val);
    return var.min_val;
  }
  std::uniform_int_distribution<int64_t> dist(var.min_val, var.max_val);
  return dist(rng_);
}

double ConstraintSolver::GenerateRandRealValue(RandVariable& var) {
  // 18.4.1: random real values are uniformly distributed over their range, so
  // the probability of landing in any subrange is proportional only to its
  // width. A uniform_real_distribution over [real_min, real_max) realizes that
  // flat density directly. A degenerate or inverted range collapses to the
  // lower bound rather than invoking the distribution on an empty interval.
  if (!(var.real_min < var.real_max)) return var.real_min;
  std::uniform_real_distribution<double> dist(var.real_min, var.real_max);
  return dist(rng_);
}

namespace {

// 18.5.3: the stage-1 weight of a distribution item. The ':=' operator on a
// range assigns the weight to each element, so the range's total weight is the
// per-element weight times the element count. A single value, or a range or
// default weighted with ':/', contributes its weight as a whole.
uint64_t DistItemWeight(const DistWeight& w) {
  if (w.is_range && w.per_element) {
    int64_t size = w.hi - w.lo + 1;
    if (size <= 0) return 0;
    return static_cast<uint64_t>(w.weight) * static_cast<uint64_t>(size);
  }
  return w.weight;
}

int64_t DistItemRepresentative(const DistWeight& w) {
  return w.is_range ? w.lo : w.value;
}

}  // namespace

// 18.5.3: a value covered only by 'default :/ weight' is any domain value not
// named by another item. Draw uniformly from [domain_lo, domain_hi], rejecting
// values already covered by a non-default item.
int64_t ConstraintSolver::SampleDefaultValue(
    const std::vector<DistWeight>& weights, int64_t domain_lo,
    int64_t domain_hi) {
  if (domain_hi < domain_lo) return domain_lo;
  auto covered = [&weights](int64_t v) {
    for (const auto& w : weights) {
      if (w.is_default) continue;
      if (w.is_range) {
        if (v >= w.lo && v <= w.hi) return true;
      } else if (v == w.value) {
        return true;
      }
    }
    return false;
  };
  std::uniform_int_distribution<int64_t> within(domain_lo, domain_hi);
  for (int attempt = 0; attempt < 1000; ++attempt) {
    int64_t v = within(rng_);
    if (!covered(v)) return v;
  }
  return domain_lo;
}

// 18.5.3: select a value from a distribution. Stage 1 chooses an item with
// probability proportional to its (unsigned) weight; stage 2 resolves the
// chosen item to a concrete value. Because the per-item probabilities add, a
// value named by several items accumulates their weights, and a value carrying
// a zero weight in one item is still reachable through another nonzero item.
// Only values named by the set (or, with a default item, the rest of the
// domain) are ever produced.
int64_t ConstraintSolver::DistributionSample(
    const std::vector<DistWeight>& weights, int64_t domain_lo,
    int64_t domain_hi) {
  if (weights.empty()) return 0;
  uint64_t total = 0;
  for (const auto& w : weights) total += DistItemWeight(w);
  if (total == 0) return DistItemRepresentative(weights.front());

  std::uniform_int_distribution<uint64_t> select(0, total - 1);
  uint64_t pick = select(rng_);
  uint64_t accum = 0;
  for (const auto& w : weights) {
    accum += DistItemWeight(w);
    if (pick < accum) {
      if (w.is_default)
        return SampleDefaultValue(weights, domain_lo, domain_hi);
      if (w.is_range) {
        std::uniform_int_distribution<int64_t> within(w.lo, w.hi);
        return within(rng_);
      }
      return w.value;
    }
  }
  return DistItemRepresentative(weights.back());
}

// 18.5.3: sample a distribution constraint, bounding a default item by the
// target variable's declared domain when it is known.
int64_t ConstraintSolver::SampleDist(const ConstraintExpr& c) {
  auto it = variables_.find(c.var_name);
  int64_t lo = it != variables_.end() ? it->second.min_val : 0;
  int64_t hi = it != variables_.end() ? it->second.max_val : 0xFFFF;
  return DistributionSample(c.dist_weights, lo, hi);
}

bool ConstraintSolver::HasDistOnRandc() const {
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) {
      if (c.kind != ConstraintKind::kDist) continue;
      auto it = variables_.find(c.var_name);
      if (it != variables_.end() &&
          it->second.qualifier == RandQualifier::kRandc) {
        return true;
      }
    }
  }
  return false;
}

// 18.5.3: a dist expression requires that it contain at least one rand
// variable. The distribution names the single variable it constrains, so that
// target must resolve to an active rand variable; a target the solver does not
// know, or one declared without the rand qualifier, leaves the distribution
// with no rand variable to act on.
bool ConstraintSolver::DistLacksRandVariable() const {
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) {
      if (c.kind != ConstraintKind::kDist) continue;
      auto it = variables_.find(c.var_name);
      if (it == variables_.end() ||
          it->second.qualifier == RandQualifier::kNone) {
        return true;
      }
    }
  }
  return false;
}

// 18.5.4: no randc variable shall appear in the group of a uniqueness
// constraint. Scan every enabled unique constraint and report a randc member.
bool ConstraintSolver::HasRandcInUnique() const {
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) {
      if (c.kind != ConstraintKind::kUnique) continue;
      for (const auto& name : c.unique_vars) {
        auto it = variables_.find(name);
        if (it != variables_.end() &&
            it->second.qualifier == RandQualifier::kRandc) {
          return true;
        }
      }
    }
  }
  return false;
}

// 18.5.4: all members of a uniqueness constraint group shall be of equivalent
// type. Compare the known members of each enabled unique constraint against the
// first known member: a difference in real-ness or bit width means the group
// mixes inequivalent types. Members the solver does not know are left out of the
// comparison, mirroring the lenient treatment elsewhere in the solver.
bool ConstraintSolver::UniqueMembersNotEquivalentType() const {
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) {
      if (c.kind != ConstraintKind::kUnique) continue;
      const RandVariable* ref = nullptr;
      for (const auto& name : c.unique_vars) {
        auto it = variables_.find(name);
        if (it == variables_.end()) continue;
        if (ref == nullptr) {
          ref = &it->second;
          continue;
        }
        if (it->second.is_real != ref->is_real ||
            it->second.width != ref->width) {
          return true;
        }
      }
    }
  }
  return false;
}

GuardValue GuardAnd(GuardValue a, GuardValue b) {
  // Figure 18-3 conjunction: a FALSE subexpression forces FALSE; otherwise an
  // ERROR subexpression forces ERROR; otherwise a RANDOM subexpression yields
  // RANDOM; with neither present the result is TRUE.
  if (a == GuardValue::kFalse || b == GuardValue::kFalse)
    return GuardValue::kFalse;
  if (a == GuardValue::kError || b == GuardValue::kError)
    return GuardValue::kError;
  if (a == GuardValue::kRandom || b == GuardValue::kRandom)
    return GuardValue::kRandom;
  return GuardValue::kTrue;
}

GuardValue GuardOr(GuardValue a, GuardValue b) {
  // Figure 18-3 disjunction: a TRUE subexpression forces TRUE; otherwise an
  // ERROR subexpression forces ERROR; otherwise a RANDOM subexpression yields
  // RANDOM; with neither present the result is FALSE.
  if (a == GuardValue::kTrue || b == GuardValue::kTrue)
    return GuardValue::kTrue;
  if (a == GuardValue::kError || b == GuardValue::kError)
    return GuardValue::kError;
  if (a == GuardValue::kRandom || b == GuardValue::kRandom)
    return GuardValue::kRandom;
  return GuardValue::kFalse;
}

GuardValue GuardNot(GuardValue a) {
  // Figure 18-3 negation: ERROR and RANDOM pass through unchanged; TRUE and
  // FALSE are swapped.
  switch (a) {
    case GuardValue::kFalse:
      return GuardValue::kTrue;
    case GuardValue::kTrue:
      return GuardValue::kFalse;
    case GuardValue::kError:
      return GuardValue::kError;
    case GuardValue::kRandom:
      return GuardValue::kRandom;
  }
  return GuardValue::kError;
}

GuardOutcome GuardFinalOutcome(GuardValue final_value) {
  // 18.5.12: the final value of the evaluated predicate determines the outcome.
  switch (final_value) {
    case GuardValue::kTrue:
      return GuardOutcome::kUnconditional;
    case GuardValue::kFalse:
      return GuardOutcome::kEliminated;
    case GuardValue::kError:
      return GuardOutcome::kError;
    case GuardValue::kRandom:
      return GuardOutcome::kConditional;
  }
  return GuardOutcome::kError;
}

GuardValue EvaluateGuard(
    const GuardPredicate& pred,
    const std::unordered_map<std::string, int64_t>& values) {
  // 18.5.12: apply the operators recursively until all subexpressions are
  // evaluated. A malformed node (a leaf without a function, a negation or a
  // missing operand) is treated as an evaluation error.
  switch (pred.op) {
    case GuardPredicate::Op::kLeaf:
      return pred.leaf_fn ? pred.leaf_fn(values) : GuardValue::kError;
    case GuardPredicate::Op::kNot:
      return pred.operands.empty()
                 ? GuardValue::kError
                 : GuardNot(EvaluateGuard(pred.operands.front(), values));
    case GuardPredicate::Op::kAnd: {
      GuardValue acc = GuardValue::kTrue;
      for (const auto& operand : pred.operands)
        acc = GuardAnd(acc, EvaluateGuard(operand, values));
      return acc;
    }
    case GuardPredicate::Op::kOr: {
      GuardValue acc = GuardValue::kFalse;
      for (const auto& operand : pred.operands)
        acc = GuardOr(acc, EvaluateGuard(operand, values));
      return acc;
    }
  }
  return GuardValue::kError;
}

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

static void CollectConstraints(const std::vector<ConstraintBlock>& blocks,
                               const std::vector<ConstraintExpr>& extra,
                               std::vector<const ConstraintExpr*>& hard,
                               std::vector<const ConstraintExpr*>& soft) {
  for (const auto& block : blocks) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) {
      if (c.kind == ConstraintKind::kSoft) {
        soft.push_back(&c);
      } else {
        hard.push_back(&c);
      }
    }
  }
  for (const auto& c : extra) {
    if (c.kind == ConstraintKind::kSoft) {
      soft.push_back(&c);
    } else {
      hard.push_back(&c);
    }
  }
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
  // operand for the method. Begin from the operand's identity so a fold over any
  // number of elements is well defined, then combine each element in turn.
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

  // 18.5.7.2: the reduction returns a single value of the array element type, or
  // the type of the with-clause expression when one is specified. Truncate the
  // fold to that result type's width so a sum that would overflow the element
  // type wraps, while a wider with-clause type (e.g. int'(item)) preserves it.
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

bool ConstraintSolver::Solve() { return SolveWith({}); }

bool ConstraintSolver::Check(const std::vector<ConstraintExpr>& constraints) {
  // 18.12: the no-argument scope randomize is a pure checker. Unlike SolveWith,
  // it never generates a new value for any variable: each variable's current
  // value is taken as is, and the constraints are only evaluated against those
  // values. Every constraint expression is evaluated and the call fails the
  // moment one of them is false, succeeding only when every one holds.
  guard_error_ = false;
  for (const auto& [name, var] : variables_) {
    values_[name] = var.value;
  }
  return CheckAllConstraints(constraints, /*include_soft=*/true);
}

bool ConstraintSolver::InlineConstraintCheck(
    const std::vector<ConstraintExpr>& constraints) {
  // 18.11.1: the null argument empties the active random set. Force every
  // variable into state-variable status — regardless of its declared rand or
  // randc qualifier or its current rand_mode — so the solver randomizes none of
  // them for this call.
  for (auto& entry : variables_) {
    entry.second.enabled = false;
  }
  // With nothing left to randomize, the call is a pure checker: it takes each
  // member's current value as is and only evaluates whether the constraints are
  // satisfied, returning 1 when they all hold and 0 otherwise. The checker
  // mechanics are exactly those of the no-argument checker, so defer to it.
  return Check(constraints);
}

void ConstraintSolver::ApplyDirectConstraints(
    const std::vector<ConstraintExpr>& extra, bool include_soft) {
  auto apply = [this](const ConstraintExpr& c) {
    if (c.kind == ConstraintKind::kEqual) {
      values_[c.var_name] = c.lo;
    } else if (c.kind == ConstraintKind::kSetMembership) {
      if (!c.set_values.empty()) {
        std::uniform_int_distribution<size_t> pick(0, c.set_values.size() - 1);
        values_[c.var_name] = c.set_values[pick(rng_)];
      }
    }
  };
  // 18.5.13: when the soft constraints are still active, seed their inner
  // expression_or_dist exactly as a hard constraint so a satisfiable soft
  // preference is honored. A hard constraint applied afterward takes precedence
  // and overwrites any conflicting soft seed, leaving the conflicting soft to
  // be discarded by the include_soft-clear retry.
  auto seed = [&](const ConstraintExpr& c) {
    if (include_soft && c.kind == ConstraintKind::kSoft && c.inner) {
      apply(*c.inner);
    } else {
      apply(c);
    }
  };
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) seed(c);
  }
  for (const auto& c : extra) seed(c);
}

bool ConstraintSolver::SolveWith(
    const std::vector<ConstraintExpr>& inline_constraints) {
  // 18.5.3: a dist operation shall not be applied to a randc variable, and a
  // dist expression requires at least one rand variable. A distribution that
  // violates either limitation makes randomization fail outright.
  if (HasDistOnRandc()) return false;
  if (DistLacksRandVariable()) return false;

  // 18.5.4: a uniqueness constraint group may not contain a randc variable and
  // all of its members shall be of equivalent type. An illegal group makes
  // randomization fail outright.
  if (HasRandcInUnique()) return false;
  if (UniqueMembersNotEquivalentType()) return false;

  if (pre_randomize_) pre_randomize_();

  // 18.5.13: hard constraints shall always be satisfied or randomization fails.
  // First try to satisfy them together with the soft constraints. If no such
  // solution exists, discard the soft constraints — a discarded soft constraint
  // is treated as if replaced by the value 1 (true): it need not hold and has
  // no effect on the solution distribution — and solve the remaining hard set.
  bool solved = SolveIterative(inline_constraints, /*include_soft=*/true);
  if (!solved && !guard_error_) {
    solved = SolveIterative(inline_constraints, /*include_soft=*/false);
  }

  if (solved && post_randomize_) post_randomize_();
  return solved;
}

void ConstraintSolver::ApplyDistConstraints() {
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) {
      if (c.kind == ConstraintKind::kDist) {
        values_[c.var_name] = SampleDist(c);
      }
    }
  }
}

bool ConstraintSolver::SolveIterative(
    const std::vector<ConstraintExpr>& extra, bool include_soft) {
  static constexpr int kMaxAttempts = 500;
  guard_error_ = false;
  for (int attempt = 0; attempt < kMaxAttempts; ++attempt) {
    values_.clear();
    real_values_.clear();
    // 18.8 / 18.5.8: an inactive variable (rand_mode() OFF) is not one of the
    // active random variables, so it is not randomized. The solver instead
    // treats it as a state variable: its current value is seeded as a constant
    // before solving, so a global constraint relating it to an active variable
    // is evaluated against that fixed value rather than dropped.
    for (auto& [name, var] : variables_) {
      // 18.4.1: a real variable's value lives in real_values_, not the integral
      // values_ map; an inactive one likewise holds its current real value.
      if (var.is_real) {
        if (!var.enabled) real_values_[name] = var.real_value;
        continue;
      }
      if (!var.enabled) values_[name] = var.value;
    }
    ApplyDistConstraints();
    ApplyDirectConstraints(extra, include_soft);
    // 18.4.2: the cyclic (randc) variables shall be solved before the
    // noncyclical rand variables. Draw every active randc value first so that
    // the rand variables that follow are solved with the cyclic values already
    // committed for this attempt; a constraint set that mixes rand and randc
    // therefore resolves the randc variables first, as the cyclic semantics
    // require.
    for (auto& [name, var] : variables_) {
      if (!var.enabled || var.is_real) continue;
      if (var.qualifier != RandQualifier::kRandc) continue;
      if (values_.find(name) != values_.end()) continue;
      values_[name] = GenerateRandValue(var);
    }
    // 18.5.7.1: an array's size method is solved with the size constraints,
    // ahead of the iterative (foreach) constraints over that array. Commit
    // every active array-size variable here, before the general rand pass
    // below, so that a foreach reading the size sees the value already chosen
    // and treats it as a state variable rather than one it may itself
    // constrain. The general pass then skips these already-committed variables.
    for (auto& [name, var] : variables_) {
      if (!var.enabled || var.is_real) continue;
      if (!var.is_array_size) continue;
      if (var.qualifier == RandQualifier::kRandc) continue;
      if (values_.find(name) != values_.end()) continue;
      values_[name] = GenerateRandValue(var);
    }
    for (auto& [name, var] : variables_) {
      if (!var.enabled) continue;
      // 18.4.1: draw an active real variable from its uniform real range.
      if (var.is_real) {
        real_values_[name] = GenerateRandRealValue(var);
        continue;
      }
      // randc variables are already committed above; skip them here.
      if (values_.find(name) != values_.end()) continue;
      values_[name] = GenerateRandValue(var);
    }
    if (CheckAllConstraints(extra, include_soft)) return true;
    // 18.5.12: an ERROR guard fails randomize() outright; do not retry it.
    if (guard_error_) return false;
  }
  return false;
}

int64_t ConstraintSolver::GetValue(std::string_view name) const {
  auto it = values_.find(std::string(name));
  return (it != values_.end()) ? it->second : 0;
}

double ConstraintSolver::GetRealValue(std::string_view name) const {
  auto it = real_values_.find(std::string(name));
  return (it != real_values_.end()) ? it->second : 0.0;
}

}
