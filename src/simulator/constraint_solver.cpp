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

void ConstraintSolver::AddSolveBefore(const std::vector<std::string>& before,
                                      const std::vector<std::string>& after) {
  // 18.5.9: 'solve before_list before after_list' constrains every variable of
  // the first list to be solved ahead of every variable of the second, so
  // record the cross product of ordering edges.
  for (const auto& b : before) {
    for (const auto& a : after) {
      solve_before_edges_.emplace_back(b, a);
    }
  }
}

void ConstraintSolver::AddFunctionArgPriority(
    const std::vector<std::string>& higher,
    const std::vector<std::string>& lower) {
  // 18.5.11: every higher-priority variable is solved before every variable of
  // the constraint that used it as a function argument, so record the cross
  // product of priority edges. A variable that is both higher- and lower-named
  // (it depends on itself) would form a degenerate cycle, which the cycle check
  // catches and reports.
  for (const auto& h : higher) {
    for (const auto& l : lower) {
      function_arg_priority_edges_.emplace_back(h, l);
    }
  }
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
    if (block.name != block_name) continue;
    block.enabled = enabled;
    // 18.5.10: turning a static constraint on or off affects every instance of
    // the class, so record the change in the shared state the other instances
    // read from.
    if (block.shared_enabled) *block.shared_enabled = enabled;
  }
}

bool ConstraintSolver::GetConstraintMode(std::string_view block_name) const {
  for (const auto& block : blocks_) {
    if (block.name != block_name) continue;
    // 18.5.10: a static constraint's on/off state is the one shared across all
    // instances; report that rather than this instance's cached flag.
    return block.shared_enabled ? *block.shared_enabled : block.enabled;
  }
  return false;
}

void ConstraintSolver::RefreshStaticBlockState() {
  for (auto& block : blocks_) {
    if (block.shared_enabled) block.enabled = *block.shared_enabled;
  }
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

namespace {

// 18.4.2: draw a randc value from an enum's named constants, cycling through
// the permutation before repeating. Reject already-drawn values; once the full
// set has been seen, clear the history and start a fresh permutation. Falls
// back to the first unseen value (then to a reset to the first constant) if the
// random draws keep colliding.
int64_t DrawRandcEnumValue(RandVariable& var,
                           std::unordered_set<int64_t>& history,
                           std::mt19937& rng) {
  if (history.size() >= var.enum_values.size()) {
    history.clear();
  }
  for (int attempt = 0; attempt < 1000; ++attempt) {
    std::uniform_int_distribution<size_t> pick(0, var.enum_values.size() - 1);
    int64_t val = var.enum_values[pick(rng)];
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

// 18.4.2: draw a randc value from the variable's declared integer range,
// cycling through the permutation before repeating. Reject already-drawn
// values; once the full range has been seen, clear the history and start a
// fresh permutation. Falls back to the first unseen value (then to a reset to
// the range minimum) if the random draws keep colliding.
int64_t DrawRandcRangeValue(RandVariable& var,
                            std::unordered_set<int64_t>& history,
                            std::mt19937& rng) {
  int64_t range_size = var.max_val - var.min_val + 1;

  if (static_cast<int64_t>(history.size()) >= range_size) {
    history.clear();
  }

  for (int attempt = 0; attempt < 1000; ++attempt) {
    std::uniform_int_distribution<int64_t> dist(var.min_val, var.max_val);
    int64_t val = dist(rng);
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

}  // namespace

int64_t ConstraintSolver::GenerateRandValue(RandVariable& var) {
  // 18.4.2: the randc permutation's no-repeat property spans successive
  // randomize() calls, so the drawn-value history must outlive any single
  // solve. When shared_randc_state is attached the history lives there — a
  // caller that rebuilds the solver each call points it at externally owned,
  // persistent state so the same cycle advances across calls (a nonstatic
  // variable uses its object's own history; a static variable shares one
  // history across every instance of the class). When it is null the history
  // is per-solver, which suffices for repeated solves on one solver object.
  // Bind the active history once here and advance it below, so the same
  // draw-and-reject logic serves every case.
  std::unordered_set<int64_t>& history =
      var.shared_randc_state ? *var.shared_randc_state : var.randc_history;
  // 18.3: a random variable of enum type must take one of the enum's named
  // constants. The 18.4 exception (an enum member of a packed struct/union)
  // clears apply_enum_restriction, in which case the named set is ignored and
  // the value is drawn from the full declared range below.
  if (!var.enum_values.empty() && var.apply_enum_restriction) {
    if (var.qualifier == RandQualifier::kRandc) {
      return DrawRandcEnumValue(var, history, rng_);
    }
    std::uniform_int_distribution<size_t> pick(0, var.enum_values.size() - 1);
    return var.enum_values[pick(rng_)];
  }
  if (var.qualifier == RandQualifier::kRandc) {
    return DrawRandcRangeValue(var, history, rng_);
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

// 18.5.3: a value is covered by the distribution's non-default items when it
// equals a named single value or falls inside a named range. Default items name
// no specific value, so they never cover anything here.
bool DistValueCovered(const std::vector<DistWeight>& weights, int64_t v) {
  for (const auto& w : weights) {
    if (w.is_default) continue;
    if (w.is_range) {
      if (v >= w.lo && v <= w.hi) return true;
    } else if (v == w.value) {
      return true;
    }
  }
  return false;
}

}  // namespace

// 18.5.3: a value covered only by 'default :/ weight' is any domain value not
// named by another item. Draw uniformly from [domain_lo, domain_hi], rejecting
// values already covered by a non-default item.
int64_t ConstraintSolver::SampleDefaultValue(
    const std::vector<DistWeight>& weights, int64_t domain_lo,
    int64_t domain_hi) {
  if (domain_hi < domain_lo) return domain_lo;
  std::uniform_int_distribution<int64_t> within(domain_lo, domain_hi);
  for (int attempt = 0; attempt < 1000; ++attempt) {
    int64_t v = within(rng_);
    if (!DistValueCovered(weights, v)) return v;
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

namespace {

// 18.5.4: a uniqueness group violates the no-randc rule when any of its known
// members is declared randc.
bool UniqueGroupHasRandcMember(
    const ConstraintExpr& c,
    const std::unordered_map<std::string, RandVariable>& variables) {
  for (const auto& name : c.unique_vars) {
    auto it = variables.find(name);
    if (it != variables.end() &&
        it->second.qualifier == RandQualifier::kRandc) {
      return true;
    }
  }
  return false;
}

// 18.5.4: a uniqueness group mixes inequivalent types when any known member
// differs from the first known member in real-ness or bit width. Members the
// solver does not know are skipped, mirroring the lenient treatment elsewhere.
bool UniqueGroupHasInequivalentTypes(
    const ConstraintExpr& c,
    const std::unordered_map<std::string, RandVariable>& variables) {
  const RandVariable* ref = nullptr;
  for (const auto& name : c.unique_vars) {
    auto it = variables.find(name);
    if (it == variables.end()) continue;
    if (ref == nullptr) {
      ref = &it->second;
      continue;
    }
    if (it->second.is_real != ref->is_real || it->second.width != ref->width) {
      return true;
    }
  }
  return false;
}

}  // namespace

// 18.5.4: no randc variable shall appear in the group of a uniqueness
// constraint. Scan every enabled unique constraint and report a randc member.
bool ConstraintSolver::HasRandcInUnique() const {
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) {
      if (c.kind != ConstraintKind::kUnique) continue;
      if (UniqueGroupHasRandcMember(c, variables_)) return true;
    }
  }
  return false;
}

// 18.5.4: all members of a uniqueness constraint group shall be of equivalent
// type. Compare the known members of each enabled unique constraint against the
// first known member: a difference in real-ness or bit width means the group
// mixes inequivalent types. Members the solver does not know are left out of
// the comparison, mirroring the lenient treatment elsewhere in the solver.
bool ConstraintSolver::UniqueMembersNotEquivalentType() const {
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) {
      if (c.kind != ConstraintKind::kUnique) continue;
      if (UniqueGroupHasInequivalentTypes(c, variables_)) return true;
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

}  // namespace delta
