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

bool ConstraintSolver::ConstrainsAlone(const ConstraintExpr& c,
                                       const std::string& name) const {
  if (c.kind == ConstraintKind::kSoft || !ConstraintNames(c, name))
    return false;
  std::vector<std::string> named;
  CollectNamed(c, named);
  return std::none_of(named.begin(), named.end(), [&](const std::string& n) {
    auto vit = variables_.find(n);
    return n != name && vit != variables_.end() && vit->second.enabled;
  });
}

std::vector<int64_t> ConstraintSolver::AdmittedValues(
    const std::string& name, const std::vector<const ConstraintExpr*>& own,
    const std::vector<int64_t>& domain) {
  auto saved = values_.find(name);
  bool had = saved != values_.end();
  int64_t saved_value = had ? saved->second : 0;
  std::vector<int64_t> out;
  for (int64_t v : domain) {
    values_[name] = v;
    if (std::all_of(own.begin(), own.end(), [&](const ConstraintExpr* c) {
          return EvalConstraint(*c);
        }))
      out.push_back(v);
  }
  if (had) {
    values_[name] = saved_value;
  } else {
    values_.erase(name);
  }
  return out;
}

bool ConstraintSolver::OwnAdmissibleValues(
    const RandVariable& var, const std::vector<ConstraintExpr>& extra,
    bool need_custom, std::vector<int64_t>& out) {
  // The domain is judged first, as the constraints a wide one is held to are
  // never enumerated.
  std::vector<int64_t> domain;
  if (!EnumeratedDomain(var, domain)) return false;
  std::vector<const ConstraintExpr*> own;
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) {
      if (ConstrainsAlone(c, var.name)) own.push_back(&c);
    }
  }
  for (const auto& c : extra) {
    if (ConstrainsAlone(c, var.name)) own.push_back(&c);
  }
  bool custom =
      std::any_of(own.begin(), own.end(), [](const ConstraintExpr* c) {
        return c->kind == ConstraintKind::kCustom;
      });
  if (own.empty() || (need_custom && !custom)) return false;
  out = AdmittedValues(var.name, own, domain);
  return !out.empty();
}

bool ConstraintSolver::DrawAdmissibleRandc(
    RandVariable& var, const std::vector<ConstraintExpr>& extra, int64_t& out) {
  std::vector<int64_t> admissible;
  std::unordered_set<int64_t>& history =
      var.shared_randc_state ? *var.shared_randc_state : var.randc_history;
  std::vector<int64_t>& began =
      var.shared_randc_domain ? *var.shared_randc_domain : var.randc_domain;
  if (!OwnAdmissibleValues(var, extra, /*need_custom=*/false, admissible)) {
    // Constraints that no longer narrow the variable alone end the
    // permutation they began.
    if (!began.empty()) {
      history.clear();
      began.clear();
    }
    return false;
  }
  // Constraints admitting other values than when the permutation began have
  // changed, so the permutation is recomputed.
  if (began != admissible) {
    history.clear();
    began = admissible;
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
