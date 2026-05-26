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
  // 18.3: a random variable of enum type must take one of the enum's named
  // constants. The 18.4 exception (an enum member of a packed struct/union)
  // clears apply_enum_restriction, in which case the named set is ignored and
  // the value is drawn from the full declared range below.
  if (!var.enum_values.empty() && var.apply_enum_restriction) {
    if (var.qualifier == RandQualifier::kRandc) {
      if (var.randc_history.size() >= var.enum_values.size()) {
        var.randc_history.clear();
      }
      for (int attempt = 0; attempt < 1000; ++attempt) {
        std::uniform_int_distribution<size_t> pick(0, var.enum_values.size() - 1);
        int64_t val = var.enum_values[pick(rng_)];
        if (var.randc_history.find(val) == var.randc_history.end()) {
          var.randc_history.insert(val);
          return val;
        }
      }
      for (int64_t v : var.enum_values) {
        if (var.randc_history.find(v) == var.randc_history.end()) {
          var.randc_history.insert(v);
          return v;
        }
      }
      var.randc_history.clear();
      var.randc_history.insert(var.enum_values.front());
      return var.enum_values.front();
    }
    std::uniform_int_distribution<size_t> pick(0, var.enum_values.size() - 1);
    return var.enum_values[pick(rng_)];
  }
  if (var.qualifier == RandQualifier::kRandc) {
    int64_t range_size = var.max_val - var.min_val + 1;

    if (static_cast<int64_t>(var.randc_history.size()) >= range_size) {
      var.randc_history.clear();
    }

    for (int attempt = 0; attempt < 1000; ++attempt) {
      std::uniform_int_distribution<int64_t> dist(var.min_val, var.max_val);
      int64_t val = dist(rng_);
      if (var.randc_history.find(val) == var.randc_history.end()) {
        var.randc_history.insert(val);
        return val;
      }
    }

    for (int64_t v = var.min_val; v <= var.max_val; ++v) {
      if (var.randc_history.find(v) == var.randc_history.end()) {
        var.randc_history.insert(v);
        return v;
      }
    }
    var.randc_history.clear();
    var.randc_history.insert(var.min_val);
    return var.min_val;
  }
  std::uniform_int_distribution<int64_t> dist(var.min_val, var.max_val);
  return dist(rng_);
}

int64_t ConstraintSolver::DistributionSample(
    const std::vector<DistWeight>& weights) {
  if (weights.empty()) return 0;
  uint64_t total = 0;
  for (const auto& w : weights) total += w.weight;
  if (total == 0) return weights[0].value;

  std::uniform_int_distribution<uint64_t> dist(0, total - 1);
  uint64_t pick = dist(rng_);
  uint64_t accum = 0;
  for (const auto& w : weights) {
    accum += w.weight;
    if (pick < accum) return w.value;
  }
  return weights.back().value;
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
    values_[expr.var_name] = DistributionSample(expr.dist_weights);
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
    const std::vector<ConstraintExpr>& extra) {
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
  for (const auto& sub : expr.sub_constraints) {
    if (!EvalConstraint(sub)) return false;
  }
  return true;
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

void ConstraintSolver::ApplyDirectConstraints(
    const std::vector<ConstraintExpr>& extra) {
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
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) apply(c);
  }
  for (const auto& c : extra) apply(c);
}

bool ConstraintSolver::SolveWith(
    const std::vector<ConstraintExpr>& inline_constraints) {
  if (pre_randomize_) pre_randomize_();

  values_.clear();

  ApplyDistConstraints();

  ApplyDirectConstraints(inline_constraints);

  for (auto& [name, var] : variables_) {
    if (!var.enabled) continue;
    if (values_.find(name) != values_.end()) continue;
    values_[name] = GenerateRandValue(var);
  }

  bool solved = SolveIterative(inline_constraints);

  if (solved && post_randomize_) post_randomize_();
  return solved;
}

void ConstraintSolver::ApplyDistConstraints() {
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) {
      if (c.kind == ConstraintKind::kDist) {
        values_[c.var_name] = DistributionSample(c.dist_weights);
      }
    }
  }
}

bool ConstraintSolver::SolveIterative(
    const std::vector<ConstraintExpr>& extra) {
  static constexpr int kMaxAttempts = 500;
  guard_error_ = false;
  for (int attempt = 0; attempt < kMaxAttempts; ++attempt) {
    if (CheckAllConstraints(extra)) return true;
    // 18.5.12: an ERROR guard fails randomize() outright; do not retry it.
    if (guard_error_) return false;

    values_.clear();
    ApplyDistConstraints();
    ApplyDirectConstraints(extra);
    for (auto& [name, var] : variables_) {
      if (!var.enabled) continue;
      if (values_.find(name) != values_.end()) continue;
      values_[name] = GenerateRandValue(var);
    }
  }
  return false;
}

int64_t ConstraintSolver::GetValue(std::string_view name) const {
  auto it = values_.find(std::string(name));
  return (it != values_.end()) ? it->second : 0;
}

}
