#include <cstddef>
#include <cstdint>
#include <random>
#include <string>
#include <vector>

#include "simulator/constraint_solver.h"
#include "simulator/constraint_solver_internal.h"

namespace delta {

namespace {

// 18.5.3: the draws tried within one distribution item before the item is
// taken to hold no value the constraints on its variable admit. A single value
// is decided by its first draw; a range of three values two of which another
// constraint excludes is passed over wrongly once in (2/3)**32 draws.
constexpr int kDrawsPerItem = 32;

constexpr size_t kNoItem = SIZE_MAX;

// 18.5.3: the stage-1 weight of a distribution item. The ':=' operator on a
// range assigns the weight to each element, so the range's total weight is the
// per-element weight times the element count, counting the elements other
// constraints exclude. A single value, or a range or default weighted with
// ':/', contributes its weight as a whole, as does every range of a real
// variable, whose elements are not counted.
uint64_t DistItemWeight(const DistWeight& w, bool is_real) {
  if (w.is_range && w.per_element && !is_real) {
    int64_t size = w.hi - w.lo + 1;
    if (size <= 0) return 0;
    return static_cast<uint64_t>(w.weight) * static_cast<uint64_t>(size);
  }
  return w.weight;
}

int64_t DistItemRepresentative(const DistWeight& w) {
  return w.is_range ? w.lo : w.value;
}

// 18.5.3: stage 1 of a draw -- choose an item with probability proportional to
// its weight. kNoItem when every weight is zero, so there is nothing to draw.
size_t SelectDistItem(const std::vector<DistWeight>& weights, bool is_real,
                      std::mt19937& rng) {
  uint64_t total = 0;
  for (const auto& w : weights) total += DistItemWeight(w, is_real);
  if (total == 0) return kNoItem;
  std::uniform_int_distribution<uint64_t> select(0, total - 1);
  uint64_t pick = select(rng);
  uint64_t accum = 0;
  for (size_t i = 0; i < weights.size(); ++i) {
    accum += DistItemWeight(weights[i], is_real);
    if (pick < accum) return i;
  }
  return weights.size() - 1;
}

// 18.5.3: a value is covered by the distribution's non-default items when it
// equals a named single value or falls inside a named range. Default items name
// no specific value, so they never cover anything here.
// 6.11.3: a weighted range covers the values between its ends in the order the
// constrained variable's declared type reads them, the same order the range is
// drawn from, so a range in the top half of an unsigned domain covers what it
// names rather than nothing.
bool DistValueCovered(const std::vector<DistWeight>& weights, int64_t v,
                      bool is_signed) {
  for (const auto& w : weights) {
    if (w.is_default) continue;
    if (w.is_range) {
      if (!ValueLess(is_signed, v, w.lo) && !ValueLess(is_signed, w.hi, v))
        return true;
    } else if (v == w.value) {
      return true;
    }
  }
  return false;
}

bool DistRealCovered(const std::vector<DistWeight>& weights, double v) {
  for (const auto& w : weights) {
    if (w.is_default) continue;
    if (w.is_range ? (w.real_lo <= v && v <= w.real_hi) : v == w.real_value)
      return true;
  }
  return false;
}

}  // namespace

bool ConfinedTo(const ConstraintExpr& c, const std::string& name) {
  bool names = c.var_name == name;
  if (!c.var_name.empty() && c.var_name != name) return false;
  if (!c.cond_var.empty() && c.cond_var != name) return false;
  if (!c.unique_vars.empty() || !c.reduce_vars.empty() || !c.size_var.empty()) {
    return false;
  }
  for (const auto& r : c.ref_vars) {
    if (r != name) return false;
    names = true;
  }
  for (const auto& sub : c.sub_constraints) {
    if (!ConfinedTo(sub, name)) return false;
  }
  for (const auto& sub : c.else_constraints) {
    if (!ConfinedTo(sub, name)) return false;
  }
  return names;
}

namespace {}  // namespace

// 18.5.3: a value covered only by 'default :/ weight' is any domain value not
// named by another item. Draw uniformly from [domain_lo, domain_hi], rejecting
// values already covered by a non-default item.
int64_t ConstraintSolver::SampleDefaultValue(
    const std::vector<DistWeight>& weights, int64_t domain_lo,
    int64_t domain_hi, bool is_signed) {
  if (ValueLess(is_signed, domain_hi, domain_lo)) return domain_lo;
  for (int attempt = 0; attempt < 1000; ++attempt) {
    int64_t v = DrawUniformInRange(is_signed, domain_lo, domain_hi, rng_);
    if (!DistValueCovered(weights, v, is_signed)) return v;
  }
  return domain_lo;
}

// 18.5.3: stage 2 of a draw -- resolve the chosen item to a concrete value, a
// range uniformly and the default item from the rest of the domain.
int64_t ConstraintSolver::DrawDistItem(const DistWeight& item,
                                       const std::vector<DistWeight>& weights,
                                       int64_t domain_lo, int64_t domain_hi,
                                       bool is_signed) {
  if (item.is_default)
    return SampleDefaultValue(weights, domain_lo, domain_hi, is_signed);
  if (item.is_range)
    return DrawUniformInRange(is_signed, item.lo, item.hi, rng_);
  return item.value;
}

bool ConstraintSolver::DistValueAdmissible(
    const std::string& name, const std::vector<ConstraintExpr>& extra) const {
  auto refuses = [&](const ConstraintExpr& c) {
    return ConfinedTo(c, name) && !EvalConstraint(c);
  };
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) {
      if (refuses(c)) return false;
    }
  }
  for (const auto& c : extra) {
    if (refuses(c)) return false;
  }
  return true;
}

// 18.5.3: select a value from a distribution. Stage 1 chooses an item with
// probability proportional to its (unsigned) weight; stage 2 resolves the
// chosen item to a concrete value. Because the per-item probabilities add, a
// value named by several items accumulates their weights, and a value carrying
// a zero weight in one item is still reachable through another nonzero item.
// Only values named by the set (or, with a default item, the rest of the
// domain) are ever produced. The weight of an item applies to it as a whole,
// so a value of it another constraint excludes is redrawn within the item
// rather than costing the item its share; an item holding no admissible value
// is passed over. The last draw is handed back when no item holds one, for the
// attempt to refuse.
int64_t ConstraintSolver::SampleDist(const ConstraintExpr& c,
                                     const std::vector<ConstraintExpr>& extra) {
  auto it = variables_.find(c.var_name);
  int64_t lo = it != variables_.end() ? it->second.min_val : 0;
  int64_t hi = it != variables_.end() ? it->second.max_val : 0xFFFF;
  bool is_signed = it != variables_.end() && it->second.is_signed;
  if (c.dist_weights.empty()) return 0;
  std::vector<DistWeight> weights = c.dist_weights;
  int64_t v = DistItemRepresentative(weights.front());
  for (size_t item = SelectDistItem(weights, false, rng_); item != kNoItem;
       item = SelectDistItem(weights, false, rng_)) {
    int draws =
        weights[item].is_range || weights[item].is_default ? kDrawsPerItem : 1;
    for (int draw = 0; draw < draws; ++draw) {
      v = DrawDistItem(weights[item], weights, lo, hi, is_signed);
      values_[c.var_name] = v;
      if (DistValueAdmissible(c.var_name, extra)) return v;
    }
    weights[item].weight = 0;
  }
  return v;
}

// 18.5.3: stage 2 over a real variable -- a range is drawn uniformly over the
// reals it spans, and the default item from the domain outside every other
// item.
double ConstraintSolver::DrawRealDistItem(
    const DistWeight& item, const std::vector<DistWeight>& weights,
    double domain_lo, double domain_hi) {
  if (item.is_default) {
    if (!(domain_lo < domain_hi)) return domain_lo;
    std::uniform_real_distribution<double> draw(domain_lo, domain_hi);
    for (int attempt = 0; attempt < 1000; ++attempt) {
      double v = draw(rng_);
      if (!DistRealCovered(weights, v)) return v;
    }
    return domain_lo;
  }
  if (!item.is_range) return item.real_value;
  if (!(item.real_lo < item.real_hi)) return item.real_lo;
  std::uniform_real_distribution<double> draw(item.real_lo, item.real_hi);
  return draw(rng_);
}

// 18.5.3: a distribution over a real variable, the clause's mix of real and
// integral values. The draw within an item is admitted by the domain the
// variable's relational constraints leave it (18.4.1), which is where those
// constraints are kept for a real variable.
double ConstraintSolver::SampleRealDist(const ConstraintExpr& c) {
  auto it = variables_.find(c.var_name);
  double lo = it != variables_.end() ? it->second.real_min : 0.0;
  double hi = it != variables_.end() ? it->second.real_max : 0.0;
  if (c.dist_weights.empty()) return 0.0;
  std::vector<DistWeight> weights = c.dist_weights;
  double v = weights.front().is_range ? weights.front().real_lo
                                      : weights.front().real_value;
  for (size_t item = SelectDistItem(weights, true, rng_); item != kNoItem;
       item = SelectDistItem(weights, true, rng_)) {
    int draws =
        weights[item].is_range || weights[item].is_default ? kDrawsPerItem : 1;
    for (int draw = 0; draw < draws; ++draw) {
      v = DrawRealDistItem(weights[item], weights, lo, hi);
      if (lo <= v && v <= hi) return v;
    }
    weights[item].weight = 0;
  }
  return v;
}

void ConstraintSolver::SeedDist(const ConstraintExpr& c,
                                const std::vector<ConstraintExpr>& extra) {
  auto it = variables_.find(c.var_name);
  if (it != variables_.end() && it->second.is_real) {
    real_values_[c.var_name] = SampleRealDist(c);
    return;
  }
  values_[c.var_name] = SampleDist(c, extra);
}

}  // namespace delta
