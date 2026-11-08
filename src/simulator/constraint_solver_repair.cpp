#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <random>
#include <string>
#include <unordered_map>
#include <vector>

#include "simulator/constraint_solver.h"
#include "simulator/constraint_solver_internal.h"

namespace delta {

RandVariable Narrowed(const RandVariable& var, const ConstraintExpr& sub) {
  RandVariable narrowed = var;
  auto above = [&](int64_t c) {
    narrowed.min_val = narrowed.DomainMax(narrowed.min_val, c);
  };
  auto below = [&](int64_t c) {
    narrowed.max_val = narrowed.DomainMin(narrowed.max_val, c);
  };
  switch (sub.kind) {
    case ConstraintKind::kGreaterEqual:
      above(sub.lo);
      break;
    case ConstraintKind::kGreaterThan:
      above(static_cast<int64_t>(static_cast<uint64_t>(sub.lo) + 1));
      break;
    case ConstraintKind::kLessEqual:
      below(sub.lo);
      break;
    case ConstraintKind::kLessThan:
      below(static_cast<int64_t>(static_cast<uint64_t>(sub.lo) - 1));
      break;
    case ConstraintKind::kRange:
      above(sub.lo);
      below(sub.hi);
      break;
    default:
      break;
  }
  return narrowed;
}

bool IsComparison(ConstraintKind kind) {
  return kind == ConstraintKind::kGreaterEqual ||
         kind == ConstraintKind::kGreaterThan ||
         kind == ConstraintKind::kLessEqual ||
         kind == ConstraintKind::kLessThan || kind == ConstraintKind::kRange;
}

void ConstraintSolver::RepairConstraints(
    const std::vector<ConstraintExpr>& extra) {
  repair_extra_ = &extra;
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) RepairConstraint(c);
  }
  for (const auto& c : extra) RepairConstraint(c);
  repair_extra_ = nullptr;
}

void ConstraintSolver::RepairConstraint(const ConstraintExpr& c) {
  if (c.kind == ConstraintKind::kSoft) {
    if (SoftHonored(c)) RepairConstraint(*c.inner);
    return;
  }
  if (c.kind == ConstraintKind::kCustom) {
    ApplyCustomRepair(c);
    return;
  }
  if (c.kind == ConstraintKind::kArrayReduction) {
    RepairReduction(c);
    return;
  }
  if (c.kind == ConstraintKind::kForeach) {
    size_t count =
        ClampCountToSize(c.sub_constraints.size(), c.size_var, values_);
    for (size_t i = 0; i < count; ++i) RepairConstraint(c.sub_constraints[i]);
    return;
  }
  if (c.kind != ConstraintKind::kImplication || !c.cond_fn ||
      !c.cond_fn(values_)) {
    return;
  }
  for (const ConstraintExpr& sub : c.sub_constraints) RepairConsequent(sub);
}

void ConstraintSolver::RepairConsequent(const ConstraintExpr& sub) {
  if (sub.kind == ConstraintKind::kCustom ||
      sub.kind == ConstraintKind::kImplication) {
    RepairConstraint(sub);
    return;
  }
  if (EvalConstraint(sub) || !RepairMayWrite(sub.var_name)) return;
  auto it = variables_.find(sub.var_name);
  if (sub.kind == ConstraintKind::kEqual) {
    values_[sub.var_name] = sub.lo;
  } else if (sub.kind == ConstraintKind::kSetMembership) {
    if (sub.set_values.empty()) return;
    std::uniform_int_distribution<size_t> pick(0, sub.set_values.size() - 1);
    values_[sub.var_name] = sub.set_values[pick(rng_)];
  } else if (IsComparison(sub.kind)) {
    RandVariable narrowed = Narrowed(it->second, sub);
    if (narrowed.min_val > narrowed.max_val) return;
    values_[sub.var_name] = GenerateRandValue(narrowed);
  }
}

std::vector<int64_t> StructuredCandidates(const RandVariable& var) {
  std::vector<int64_t> out{0, var.min_val, var.max_val};
  for (uint32_t i = 0; i < var.width && i < 63; ++i) {
    auto power = static_cast<int64_t>(uint64_t{1} << i);
    out.push_back(power);
    out.push_back(power - 1);
    out.push_back(power + 1);
    if (var.is_signed) out.push_back(-power);
  }
  return out;
}

bool ConstraintSolver::RepairMayWrite(const std::string& name) const {
  if (HoldsStateValue(name)) return false;
  if (!repair_scope_.empty() && repair_scope_.count(name) == 0) return false;
  auto it = variables_.find(name);
  return it != variables_.end() && it->second.enabled && !it->second.is_real &&
         it->second.qualifier != RandQualifier::kRandc;
}

void ConstraintSolver::RepairFromCandidates(const ConstraintExpr& c) {
  const std::string& name = c.ref_vars[0];
  const RandVariable& var = variables_.find(name)->second;
  std::vector<int64_t> satisfying;
  std::unordered_map<std::string, int64_t> trial = values_;
  for (int64_t candidate : StructuredCandidates(var)) {
    if (candidate < var.min_val || candidate > var.max_val) continue;
    trial[name] = candidate;
    if (c.eval_fn(trial)) satisfying.push_back(candidate);
  }
  if (satisfying.empty()) return;
  std::uniform_int_distribution<size_t> pick(0, satisfying.size() - 1);
  values_[name] = satisfying[pick(rng_)];
}

static void NarrowBy(RandVariable& dom, ConstraintKind kind, int64_t value) {
  ConstraintExpr bound;
  bound.kind = kind == ConstraintKind::kEqual ? ConstraintKind::kRange : kind;
  bound.lo = value;
  bound.hi = value;
  dom = Narrowed(dom, bound);
}

bool ConstraintSolver::SoftHonored(const ConstraintExpr& c) const {
  return c.inner != nullptr && dropped_soft_.count(&c) == 0 &&
         disabled_soft_.count(&c) == 0;
}

bool ConstraintSolver::AntecedentHolds(const ConstraintExpr& c) const {
  if (c.cond_fn) return c.cond_fn(values_);
  auto it = values_.find(c.cond_var);
  return it != values_.end() && it->second == c.cond_value;
}

void ConstraintSolver::NarrowBoundAtValues(const ConstraintExpr& c,
                                           const std::string& name,
                                           RandVariable& dom) const {
  if (c.kind == ConstraintKind::kCustom) {
    if (!c.derive_fn) return;
    if (c.var_name == name) {
      NarrowBy(dom, c.derive_cmp, c.derive_fn(values_));
    } else if (c.co_var_name == name) {
      auto it = values_.find(c.var_name);
      if (it != values_.end())
        NarrowBy(dom, MirrorComparisonKind(c.derive_cmp), it->second);
    }
    return;
  }
  if (c.var_name != name) return;
  if (c.kind == ConstraintKind::kEqual) {
    NarrowBy(dom, ConstraintKind::kEqual, c.lo);
  } else if (IsComparison(c.kind)) {
    dom = Narrowed(dom, c);
  }
}

static void IntersectMembers(const ConstraintExpr& c,
                             std::vector<int64_t>& members, bool& has_members) {
  if (!has_members) {
    members = c.set_values;
    has_members = true;
    return;
  }
  auto absent = [&c](int64_t v) {
    return std::find(c.set_values.begin(), c.set_values.end(), v) ==
           c.set_values.end();
  };
  members.erase(std::remove_if(members.begin(), members.end(), absent),
                members.end());
}

void ConstraintSolver::NarrowAtValues(const ConstraintExpr& c,
                                      const std::string& name,
                                      RandVariable& dom,
                                      std::vector<int64_t>& members,
                                      bool& has_members) const {
  switch (c.kind) {
    case ConstraintKind::kSoft:
      if (SoftHonored(c))
        NarrowAtValues(*c.inner, name, dom, members, has_members);
      return;
    case ConstraintKind::kImplication:
      if (!AntecedentHolds(c)) return;
      for (const auto& sub : c.sub_constraints)
        NarrowAtValues(sub, name, dom, members, has_members);
      return;
    case ConstraintKind::kForeach: {
      size_t count =
          ClampCountToSize(c.sub_constraints.size(), c.size_var, values_);
      for (size_t i = 0; i < count; ++i)
        NarrowAtValues(c.sub_constraints[i], name, dom, members, has_members);
      return;
    }
    case ConstraintKind::kSetMembership:
      if (c.var_name == name) IntersectMembers(c, members, has_members);
      return;
    default:
      NarrowBoundAtValues(c, name, dom);
      return;
  }
}

static std::vector<int64_t> WithinDomain(const std::vector<int64_t>& members,
                                         const RandVariable& dom) {
  std::vector<int64_t> admitted;
  for (int64_t v : members)
    if (v >= dom.min_val && v <= dom.max_val) admitted.push_back(v);
  return admitted;
}

void ConstraintSolver::NarrowByActive(const std::string& name,
                                      RandVariable& dom,
                                      std::vector<int64_t>& members,
                                      bool& has_members) const {
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& k : block.constraints)
      NarrowAtValues(k, name, dom, members, has_members);
  }
  if (repair_extra_ == nullptr) return;
  for (const auto& k : *repair_extra_)
    NarrowAtValues(k, name, dom, members, has_members);
}

void ConstraintSolver::ApplyDerived(const ConstraintExpr& c) {
  const std::string& name =
      RepairMayWrite(c.var_name) ? c.var_name : c.co_var_name;
  if (name.empty() || !RepairMayWrite(name)) return;
  RandVariable dom = variables_.find(name)->second;
  std::vector<int64_t> members;
  bool has_members = false;
  NarrowByActive(name, dom, members, has_members);
  if (dom.min_val > dom.max_val) return;
  if (!has_members) {
    values_[name] = GenerateRandValue(dom);
    return;
  }
  std::vector<int64_t> admitted = WithinDomain(members, dom);
  if (admitted.empty()) return;
  std::uniform_int_distribution<size_t> pick(0, admitted.size() - 1);
  values_[name] = admitted[pick(rng_)];
}

static int64_t SumElementNeeded(
    const ConstraintExpr& c, const std::string& name,
    const std::unordered_map<std::string, int64_t>& values) {
  int64_t rest = 0;
  size_t count = ClampCountToSize(c.reduce_vars.size(), c.size_var, values);
  for (size_t i = 0; i < count; ++i) {
    if (c.reduce_vars[i] == name) continue;
    auto it = values.find(c.reduce_vars[i]);
    if (it != values.end()) rest += it->second;
  }
  int64_t target = c.lo;
  if (c.reduce_cmp == ConstraintKind::kLessThan) target = c.lo - 1;
  if (c.reduce_cmp == ConstraintKind::kGreaterThan) target = c.lo + 1;
  return target - rest;
}

int64_t ConstraintSolver::ReductionDistanceWith(const ConstraintExpr& c,
                                                const std::string& name,
                                                int64_t candidate) {
  values_[name] = candidate;
  if (EvalConstraint(c)) return 0;
  int64_t fold = FoldReduction(c);
  return fold > c.lo ? fold - c.lo : c.lo - fold;
}

static std::vector<int64_t> RewritingCandidates(const RandVariable& var) {
  static constexpr uint64_t kScanDomain = 4096;
  std::vector<int64_t> out;
  if (var.DomainSize() <= kScanDomain) {
    for (int64_t v = var.min_val;; ++v) {
      out.push_back(v);
      if (v == var.max_val) break;
    }
    return out;
  }
  for (int64_t candidate : StructuredCandidates(var)) {
    if (!var.DomainLess(candidate, var.min_val) &&
        !var.DomainLess(var.max_val, candidate)) {
      out.push_back(candidate);
    }
  }
  return out;
}

bool ConstraintSolver::RepairReductionElement(const ConstraintExpr& c,
                                              const std::string& name) {
  const RandVariable& var = variables_.find(name)->second;
  if (!c.reduce_with && c.reduce_op == ArrayReductionOp::kSum) {
    int64_t needed = SumElementNeeded(c, name, values_);
    if (!var.DomainLess(needed, var.min_val) &&
        !var.DomainLess(var.max_val, needed) &&
        ReductionDistanceWith(c, name, needed) == 0) {
      return true;
    }
  }
  std::vector<int64_t> satisfying;
  int64_t nearest = values_[name];
  int64_t least = -1;
  for (int64_t candidate : RewritingCandidates(var)) {
    int64_t distance = ReductionDistanceWith(c, name, candidate);
    if (distance == 0) satisfying.push_back(candidate);
    if (least < 0 || distance < least) {
      least = distance;
      nearest = candidate;
    }
  }
  if (satisfying.empty()) {
    values_[name] = nearest;
    return false;
  }
  std::uniform_int_distribution<size_t> pick(0, satisfying.size() - 1);
  values_[name] = satisfying[pick(rng_)];
  return true;
}

void ConstraintSolver::RepairReduction(const ConstraintExpr& c) {
  if (EvalConstraint(c)) return;
  size_t count = ClampCountToSize(c.reduce_vars.size(), c.size_var, values_);
  for (size_t i = 0; i < count; ++i) {
    const std::string& name = c.reduce_vars[i];
    if (RepairMayWrite(name) && RepairReductionElement(c, name)) return;
  }
}

void ConstraintSolver::ApplyCustomRepair(const ConstraintExpr& c) {
  if (c.kind != ConstraintKind::kCustom || !c.eval_fn || c.eval_fn(values_)) {
    return;
  }
  if (c.derive_fn) {
    ApplyDerived(c);
    return;
  }
  if (c.ref_vars.size() == 1 && RepairMayWrite(c.ref_vars[0])) {
    RepairFromCandidates(c);
  }
}

}  // namespace delta
