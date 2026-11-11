#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <functional>
#include <random>
#include <string>
#include <unordered_map>
#include <vector>

#include "simulator/constraint_solver.h"
#include "simulator/constraint_solver_internal.h"

namespace delta {

namespace {

struct BinaryBound {
  std::string var;
  ConstraintKind cmp;
  std::string other;
};

struct PropagationSet {
  std::vector<BinaryBound> binary;
  std::vector<const ConstraintExpr*> unary;
};

void CollectPropagated(
    const ConstraintExpr& c,
    const std::function<bool(const ConstraintExpr&)>& honored,
    const std::unordered_map<std::string, int64_t>& values,
    PropagationSet& out) {
  switch (c.kind) {
    case ConstraintKind::kSoft:
      if (honored(c)) CollectPropagated(*c.inner, honored, values, out);
      return;
    case ConstraintKind::kForeach: {
      size_t count =
          ClampCountToSize(c.sub_constraints.size(), c.size_var, values);
      for (size_t i = 0; i < count; ++i)
        CollectPropagated(c.sub_constraints[i], honored, values, out);
      return;
    }
    case ConstraintKind::kCustom:
      if (!c.derive_fn || c.co_var_name.empty()) return;
      out.binary.push_back({c.var_name, c.derive_cmp, c.co_var_name});
      out.binary.push_back(
          {c.co_var_name, MirrorComparisonKind(c.derive_cmp), c.var_name});
      return;
    case ConstraintKind::kEqual:
    case ConstraintKind::kSetMembership:
      out.unary.push_back(&c);
      return;
    default:
      if (IsComparison(c.kind)) out.unary.push_back(&c);
      return;
  }
}

void NarrowByInterval(RandVariable& dom, ConstraintKind cmp,
                      const RandVariable& other) {
  ConstraintExpr bound;
  bound.kind = cmp;
  switch (cmp) {
    case ConstraintKind::kLessThan:
    case ConstraintKind::kLessEqual:
      bound.lo = other.max_val;
      break;
    case ConstraintKind::kGreaterThan:
    case ConstraintKind::kGreaterEqual:
      bound.lo = other.min_val;
      break;
    case ConstraintKind::kEqual:
      bound.kind = ConstraintKind::kRange;
      bound.lo = other.min_val;
      bound.hi = other.max_val;
      break;
    default:
      return;
  }
  dom = Narrowed(dom, bound);
}

void PropagateIntervals(const PropagationSet& set,
                        std::unordered_map<std::string, RandVariable>& dom) {
  static constexpr int kMaxRounds = 64;
  for (int round = 0; round < kMaxRounds; ++round) {
    bool changed = false;
    for (const auto& b : set.binary) {
      auto it = dom.find(b.var);
      auto other = dom.find(b.other);
      if (it == dom.end() || other == dom.end()) continue;
      RandVariable before = it->second;
      NarrowByInterval(it->second, b.cmp, other->second);
      if (it->second.min_val != before.min_val ||
          it->second.max_val != before.max_val) {
        changed = true;
      }
    }
    if (!changed) return;
  }
}

std::vector<int64_t> AdmittedMembers(const PropagationSet& set,
                                     const std::string& name,
                                     const RandVariable& dom,
                                     bool& has_members) {
  std::vector<int64_t> members;
  has_members = false;
  for (const auto* c : set.unary) {
    if (c->kind != ConstraintKind::kSetMembership || c->var_name != name)
      continue;
    if (!has_members) {
      members = c->set_values;
      has_members = true;
      continue;
    }
    auto absent = [c](int64_t v) {
      return std::find(c->set_values.begin(), c->set_values.end(), v) ==
             c->set_values.end();
    };
    members.erase(std::remove_if(members.begin(), members.end(), absent),
                  members.end());
  }
  auto outside = [&dom](int64_t v) {
    return v < dom.min_val || v > dom.max_val;
  };
  members.erase(std::remove_if(members.begin(), members.end(), outside),
                members.end());
  return members;
}

std::unordered_map<std::string, RandVariable> Intervals(
    const PropagationSet& set,
    const std::unordered_map<std::string, RandVariable>& variables,
    const std::unordered_map<std::string, int64_t>& values) {
  std::unordered_map<std::string, RandVariable> dom;
  for (const auto& [name, var] : variables) {
    if (!var.enabled || var.is_real) continue;
    RandVariable interval = var;
    auto drawn = values.find(name);
    if (drawn != values.end()) {
      interval.min_val = drawn->second;
      interval.max_val = drawn->second;
    }
    dom.emplace(name, interval);
  }
  for (const auto* c : set.unary) {
    auto it = dom.find(c->var_name);
    if (it == dom.end() || values.count(c->var_name) != 0 ||
        c->kind == ConstraintKind::kSetMembership) {
      continue;
    }
    ConstraintExpr bound = *c;
    if (c->kind == ConstraintKind::kEqual) {
      bound.kind = ConstraintKind::kRange;
      bound.hi = c->lo;
    }
    it->second = Narrowed(it->second, bound);
  }
  return dom;
}

PropagationSet CollectPropagationSet(
    const std::vector<ConstraintBlock>& blocks,
    const std::vector<ConstraintExpr>& extra,
    const std::function<bool(const ConstraintExpr&)>& honored,
    const std::unordered_map<std::string, int64_t>& values) {
  PropagationSet set;
  for (const auto& block : blocks) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints)
      CollectPropagated(c, honored, values, set);
  }
  for (const auto& c : extra) CollectPropagated(c, honored, values, set);
  return set;
}

std::vector<std::string> PendingInRandomOrder(
    const std::unordered_map<std::string, RandVariable>& dom,
    const std::unordered_map<std::string, int64_t>& values, std::mt19937& rng) {
  std::vector<std::string> pending;
  for (const auto& [name, interval] : dom) {
    if (values.count(name) == 0 &&
        interval.qualifier != RandQualifier::kRandc &&
        interval.enum_values.empty()) {
      pending.push_back(name);
    }
  }
  std::shuffle(pending.begin(), pending.end(), rng);
  return pending;
}

bool DrawInInterval(const PropagationSet& set, const std::string& name,
                    const RandVariable& interval, std::mt19937& rng,
                    int64_t& value) {
  if (interval.min_val > interval.max_val) return false;
  bool has_members = false;
  std::vector<int64_t> members =
      AdmittedMembers(set, name, interval, has_members);
  if (has_members) {
    if (members.empty()) return false;
    std::uniform_int_distribution<size_t> pick(0, members.size() - 1);
    value = members[pick(rng)];
    return true;
  }
  value = DrawUniformInRange(interval.is_signed, interval.min_val,
                             interval.max_val, rng);
  return true;
}

void KeepSameSignednessBounds(
    const std::unordered_map<std::string, RandVariable>& dom,
    std::vector<BinaryBound>& binary) {
  auto mixed = [&dom](const BinaryBound& b) {
    auto first = dom.find(b.var);
    auto second = dom.find(b.other);
    return first == dom.end() || second == dom.end() ||
           first->second.is_signed != second->second.is_signed;
  };
  binary.erase(std::remove_if(binary.begin(), binary.end(), mixed),
               binary.end());
}

void CollectExactBounds(
    const ConstraintExpr& c,
    const std::function<bool(const ConstraintExpr&)>& honored,
    PropagationSet& out) {
  if (c.kind == ConstraintKind::kSoft) {
    if (honored(c)) CollectExactBounds(*c.inner, honored, out);
    return;
  }
  if (c.kind == ConstraintKind::kCustom) {
    if (c.derive_fn && !c.co_var_name.empty()) {
      out.binary.push_back({c.var_name, c.derive_cmp, c.co_var_name});
      out.binary.push_back(
          {c.co_var_name, MirrorComparisonKind(c.derive_cmp), c.var_name});
    }
    return;
  }
  if (c.kind == ConstraintKind::kEqual ||
      c.kind == ConstraintKind::kSetMembership || IsComparison(c.kind)) {
    out.unary.push_back(&c);
  }
}

bool NarrowToMembers(const PropagationSet& set, const std::string& name,
                     RandVariable& interval) {
  std::vector<int64_t> members;
  bool constrained = false;
  for (const auto* c : set.unary) {
    if (c->kind != ConstraintKind::kSetMembership || c->var_name != name)
      continue;
    if (!constrained) {
      members = c->set_values;
      constrained = true;
      continue;
    }
    auto absent = [c](int64_t v) {
      return std::find(c->set_values.begin(), c->set_values.end(), v) ==
             c->set_values.end();
    };
    members.erase(std::remove_if(members.begin(), members.end(), absent),
                  members.end());
  }
  if (!constrained) return true;
  bool admitted = false;
  int64_t lo = 0;
  int64_t hi = 0;
  for (int64_t v : members) {
    if (interval.DomainLess(v, interval.min_val) ||
        interval.DomainLess(interval.max_val, v)) {
      continue;
    }
    lo = admitted ? interval.DomainMin(lo, v) : v;
    hi = admitted ? interval.DomainMax(hi, v) : v;
    admitted = true;
  }
  interval.min_val = lo;
  interval.max_val = hi;
  return admitted;
}

bool AnyDomainEmpty(const PropagationSet& set,
                    std::unordered_map<std::string, RandVariable>& dom) {
  for (auto& [name, interval] : dom) {
    if (interval.DomainLess(interval.max_val, interval.min_val) ||
        !NarrowToMembers(set, name, interval)) {
      return true;
    }
  }
  return false;
}

}  // namespace

bool ConstraintSolver::HonoredBoundsConflict(
    const std::vector<ConstraintExpr>& extra) const {
  auto honored = [this](const ConstraintExpr& c) { return SoftHonored(c); };
  PropagationSet set;
  for (const auto& block : blocks_) {
    if (!block.enabled) continue;
    for (const auto& c : block.constraints) CollectExactBounds(c, honored, set);
  }
  for (const auto& c : extra) CollectExactBounds(c, honored, set);
  std::unordered_map<std::string, RandVariable> dom =
      Intervals(set, variables_, {});
  KeepSameSignednessBounds(dom, set.binary);
  if (AnyDomainEmpty(set, dom)) return true;
  PropagateIntervals(set, dom);
  return AnyDomainEmpty(set, dom);
}

ConstraintKind MirrorComparisonKind(ConstraintKind kind) {
  switch (kind) {
    case ConstraintKind::kLessThan:
      return ConstraintKind::kGreaterThan;
    case ConstraintKind::kLessEqual:
      return ConstraintKind::kGreaterEqual;
    case ConstraintKind::kGreaterThan:
      return ConstraintKind::kLessThan;
    case ConstraintKind::kGreaterEqual:
      return ConstraintKind::kLessEqual;
    default:
      return kind;
  }
}

void ConstraintSolver::DrawPropagated(
    const std::vector<ConstraintExpr>& extra) {
  auto honored = [this](const ConstraintExpr& c) { return SoftHonored(c); };
  PropagationSet set = CollectPropagationSet(blocks_, extra, honored, values_);
  std::unordered_map<std::string, RandVariable> dom =
      Intervals(set, variables_, values_);
  PropagateIntervals(set, dom);
  for (const auto& name : PendingInRandomOrder(dom, values_, rng_)) {
    RandVariable& interval = dom.find(name)->second;
    int64_t value = 0;
    if (!DrawInInterval(set, name, interval, rng_, value)) continue;
    values_[name] = value;
    interval.min_val = value;
    interval.max_val = value;
    PropagateIntervals(set, dom);
  }
}

}  // namespace delta
