#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <iterator>
#include <random>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "simulator/constraint_solver.h"

namespace delta {

// 18.4.2: a randc variable takes the next value of its permutation once per
// randomize(), whatever the attempts the other variables take, so the value
// is drawn once into `drawn` and answered from there across them.
std::function<int64_t(RandVariable&)> ConstraintSolver::RandcOncePerSolve(
    std::unordered_map<std::string, int64_t>& drawn,
    const std::vector<ConstraintExpr>& extra) {
  return [this, &drawn, &extra](RandVariable& var) {
    auto it = drawn.find(var.name);
    if (it != drawn.end()) return it->second;
    int64_t v = 0;
    if (!DrawAdmissibleRandc(var, extra, v)) v = GenerateRandValue(var);
    drawn[var.name] = v;
    return v;
  };
}

// 18.4.2: after an attempt found no solution, a randc value one of the
// constraints naming it refuses is passed over for the next of its
// permutation, and one every such constraint admits is kept.
void ConstraintSolver::PruneRefusedRandcValues(
    std::unordered_map<std::string, int64_t>& drawn,
    const std::vector<ConstraintExpr>& extra) const {
  for (auto it = drawn.begin(); it != drawn.end();) {
    it = RandcValueAdmissible(it->first, extra) ? std::next(it)
                                                : drawn.erase(it);
  }
}

// The variables the constraint `c` names, as the variable it constrains,
// among the ones it references, or in a constraint it guards.
static void CollectNamed(const ConstraintExpr& c,
                         std::vector<std::string>& out) {
  if (!c.var_name.empty()) out.push_back(c.var_name);
  out.insert(out.end(), c.ref_vars.begin(), c.ref_vars.end());
  for (const auto& sub : c.sub_constraints) CollectNamed(sub, out);
  for (const auto& sub : c.else_constraints) CollectNamed(sub, out);
}

// Whether the constraint `c` names the variable `name`, as the variable it
// constrains, among the ones it references, or in a constraint it guards.
static bool ConstraintNames(const ConstraintExpr& c, const std::string& name) {
  if (c.var_name == name) return true;
  if (std::find(c.ref_vars.begin(), c.ref_vars.end(), name) !=
      c.ref_vars.end()) {
    return true;
  }
  for (const auto& sub : c.sub_constraints) {
    if (ConstraintNames(sub, name)) return true;
  }
  for (const auto& sub : c.else_constraints) {
    if (ConstraintNames(sub, name)) return true;
  }
  return false;
}

bool ConstraintSolver::RandcValueAdmissible(
    const std::string& name, const std::vector<ConstraintExpr>& extra) const {
  auto refuses = [&](const ConstraintExpr& c) {
    return ConstraintNames(c, name) && !EvalConstraint(c);
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

// The most values a variable's admissible values are enumerated over; a
// wider domain is drawn by GenerateRandValue alone.
constexpr uint64_t kMaxEnumeratedDomain = 4096;

// The values of `var`'s domain, its enum's named constants where it is
// confined to them, into `out`; false for a real variable or a domain too
// wide to enumerate.
static bool EnumeratedDomain(const RandVariable& var,
                             std::vector<int64_t>& out) {
  bool enum_domain = !var.enum_values.empty() && var.apply_enum_restriction;
  if (var.is_real ||
      (!enum_domain && var.DomainSize() > kMaxEnumeratedDomain)) {
    return false;
  }
  if (enum_domain) {
    out = var.enum_values;
    return true;
  }
  out.clear();
  for (uint64_t offset = 0; offset < var.DomainSize(); ++offset) {
    out.push_back(
        static_cast<int64_t>(static_cast<uint64_t>(var.min_val) + offset));
  }
  return true;
}

bool ConstraintSolver::OwnAdmissibleValues(
    const RandVariable& var, const std::vector<ConstraintExpr>& extra,
    bool need_custom, std::vector<int64_t>& out) {
  // The hard constraints naming the variable and no other active random
  // variable, which decide alone whether a value is one it may take.
  std::vector<const ConstraintExpr*> own;
  bool custom = false;
  auto collect = [&](const ConstraintExpr& c) {
    if (c.kind == ConstraintKind::kSoft || !ConstraintNames(c, var.name))
      return;
    std::vector<std::string> named;
    CollectNamed(c, named);
    for (const auto& name : named) {
      auto vit = variables_.find(name);
      if (name != var.name && vit != variables_.end() && vit->second.enabled)
        return;
    }
    own.push_back(&c);
    custom = custom || c.kind == ConstraintKind::kCustom;
  };
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) collect(c);
  }
  for (const auto& c : extra) collect(c);
  std::vector<int64_t> domain;
  if (own.empty() || (need_custom && !custom) || !EnumeratedDomain(var, domain))
    return false;
  auto saved = values_.find(var.name);
  bool had = saved != values_.end();
  int64_t saved_value = had ? saved->second : 0;
  out.clear();
  for (int64_t v : domain) {
    values_[var.name] = v;
    if (std::all_of(own.begin(), own.end(), [&](const ConstraintExpr* c) {
          return EvalConstraint(*c);
        }))
      out.push_back(v);
  }
  if (had) {
    values_[var.name] = saved_value;
  } else {
    values_.erase(var.name);
  }
  return !out.empty();
}

bool ConstraintSolver::DrawAdmissibleRandc(
    RandVariable& var, const std::vector<ConstraintExpr>& extra, int64_t& out) {
  std::vector<int64_t> admissible;
  if (!OwnAdmissibleValues(var, extra, /*need_custom=*/false, admissible))
    return false;
  std::unordered_set<int64_t>& history =
      var.shared_randc_state ? *var.shared_randc_state : var.randc_history;
  // A value of the permutation in progress that the constraints now refuse
  // shows they have changed, so the permutation is recomputed.
  std::unordered_set<int64_t> admitted(admissible.begin(), admissible.end());
  for (int64_t v : history) {
    if (admitted.count(v) == 0) {
      history.clear();
      break;
    }
  }
  std::vector<int64_t> fresh;
  for (int64_t v : admissible) {
    if (history.count(v) == 0) fresh.push_back(v);
  }
  // Every admissible value has been taken: the next permutation begins.
  if (fresh.empty()) {
    history.clear();
    fresh = admissible;
  }
  std::uniform_int_distribution<size_t> pick(0, fresh.size() - 1);
  out = fresh[pick(rng_)];
  history.insert(out);
  return true;
}

void ConstraintSolver::SeedEnumerableVariables(
    const std::vector<ConstraintExpr>& extra,
    std::unordered_map<std::string, std::vector<int64_t>>& enumerated) {
  for (auto& [name, var] : variables_) {
    if (!var.enabled || var.is_real || var.qualifier == RandQualifier::kRandc ||
        values_.find(name) != values_.end()) {
      continue;
    }
    auto it = enumerated.find(name);
    if (it == enumerated.end()) {
      std::vector<int64_t> admissible;
      OwnAdmissibleValues(var, extra, /*need_custom=*/true, admissible);
      it = enumerated.emplace(name, std::move(admissible)).first;
    }
    if (it->second.empty()) continue;
    std::uniform_int_distribution<size_t> pick(0, it->second.size() - 1);
    values_[name] = it->second[pick(rng_)];
  }
}

}  // namespace delta
