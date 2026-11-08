#include "simulator/constraint_solver.h"

#include <cstddef>
#include <cstdint>
#include <random>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "simulator/constraint_solver_internal.h"

namespace delta {

int64_t DrawUniformInRange(bool is_signed, int64_t lo, int64_t hi,
                           std::mt19937& rng) {
  if (ValueLess(is_signed, hi, lo)) return lo;
  if (is_signed) {
    std::uniform_int_distribution<int64_t> dist(lo, hi);
    return dist(rng);
  }
  std::uniform_int_distribution<uint64_t> dist(static_cast<uint64_t>(lo),
                                               static_cast<uint64_t>(hi));
  return static_cast<int64_t>(dist(rng));
}

bool ValueLess(bool is_signed, int64_t a, int64_t b) {
  if (is_signed) return a < b;
  return static_cast<uint64_t>(a) < static_cast<uint64_t>(b);
}

void RandVariable::BindDomainToDeclaredRange() {
  uint32_t w = width == 0 ? 32 : width;
  if (!is_signed) {
    min_val = 0;
    max_val = w >= 64 ? static_cast<int64_t>(UINT64_MAX)
                      : static_cast<int64_t>((uint64_t{1} << w) - 1);
    return;
  }
  if (w >= 64) {
    min_val = INT64_MIN;
    max_val = INT64_MAX;
    return;
  }
  max_val = (int64_t{1} << (w - 1)) - 1;
  min_val = -(int64_t{1} << (w - 1));
}

bool RandVariable::DomainLess(int64_t a, int64_t b) const {
  return ValueLess(is_signed, a, b);
}

int64_t RandVariable::DomainMin(int64_t a, int64_t b) const {
  return DomainLess(a, b) ? a : b;
}

int64_t RandVariable::DomainMax(int64_t a, int64_t b) const {
  return DomainLess(a, b) ? b : a;
}

void RandVariable::CollapseEmptyDomain() {
  if (!DomainLess(max_val, min_val)) return;
  domain_empty = true;
  max_val = min_val;
}

uint64_t RandVariable::DomainSize() const {
  if (DomainLess(max_val, min_val)) return 0;
  uint64_t span =
      static_cast<uint64_t>(max_val) - static_cast<uint64_t>(min_val);
  return span == UINT64_MAX ? UINT64_MAX : span + 1;
}

int64_t RandVariable::DrawUniform(std::mt19937& rng) const {
  return DrawUniformInRange(is_signed, min_val, max_val, rng);
}

int64_t RandVariable::ValueFromBits(uint64_t bits) const {
  uint32_t w = width == 0 ? 32 : width;
  if (!is_signed || w >= 64) return static_cast<int64_t>(bits);
  uint64_t mask = (uint64_t{1} << w) - 1;
  bits &= mask;
  if ((bits & (uint64_t{1} << (w - 1))) != 0) bits |= ~mask;
  return static_cast<int64_t>(bits);
}

ConstraintSolver::ConstraintSolver(uint32_t seed) : rng_(seed) {}

const RandVariable* ConstraintSolver::FindVariable(
    std::string_view name) const {
  auto it = variables_.find(std::string(name));
  return it == variables_.end() ? nullptr : &it->second;
}

void ConstraintSolver::SetRandMode(std::string_view name, bool enabled) {
  auto it = variables_.find(std::string(name));
  if (it != variables_.end()) it->second.enabled = enabled;
}

bool ConstraintSolver::GetRandMode(std::string_view name) const {
  auto it = variables_.find(std::string(name));
  return (it != variables_.end()) ? it->second.enabled : false;
}

bool ConstraintSolver::HoldsStateValue(std::string_view name) const {
  auto it = variables_.find(std::string(name));
  return it != variables_.end() && !it->second.enabled;
}

void ConstraintSolver::SetAllRandMode(bool enabled) {
  for (auto& [name, var] : variables_) var.enabled = enabled;
}

void ConstraintSolver::ApplyInlineRandomList(
    const std::vector<std::string>& names) {
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
    if (block.shared_enabled) *block.shared_enabled = enabled;
  }
}

bool ConstraintSolver::GetConstraintMode(std::string_view block_name) const {
  for (const auto& block : blocks_) {
    if (block.name != block_name) continue;
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

int64_t DrawRandcRangeValue(RandVariable& var,
                            std::unordered_set<int64_t>& history,
                            std::mt19937& rng) {
  uint64_t range_size = var.DomainSize();

  if (history.size() >= range_size) {
    history.clear();
  }

  for (int attempt = 0; attempt < 1000; ++attempt) {
    int64_t val = var.DrawUniform(rng);
    if (history.find(val) == history.end()) {
      history.insert(val);
      return val;
    }
  }

  for (uint64_t offset = 0; offset < range_size; ++offset) {
    auto v = static_cast<int64_t>(static_cast<uint64_t>(var.min_val) + offset);
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
  std::unordered_set<int64_t>& history =
      var.shared_randc_state ? *var.shared_randc_state : var.randc_history;
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
  return var.DrawUniform(rng_);
}

double ConstraintSolver::GenerateRandRealValue(RandVariable& var) {
  if (!(var.real_min < var.real_max)) return var.real_min;
  std::uniform_real_distribution<double> dist(var.real_min, var.real_max);
  return dist(rng_);
}

bool ConstraintSolver::HasEmptyDomain() const {
  for (const auto& [name, var] : variables_) {
    if (var.enabled && var.domain_empty) return true;
  }
  return false;
}

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
  if (a == GuardValue::kFalse || b == GuardValue::kFalse)
    return GuardValue::kFalse;
  if (a == GuardValue::kError || b == GuardValue::kError)
    return GuardValue::kError;
  if (a == GuardValue::kRandom || b == GuardValue::kRandom)
    return GuardValue::kRandom;
  return GuardValue::kTrue;
}

GuardValue GuardOr(GuardValue a, GuardValue b) {
  if (a == GuardValue::kTrue || b == GuardValue::kTrue)
    return GuardValue::kTrue;
  if (a == GuardValue::kError || b == GuardValue::kError)
    return GuardValue::kError;
  if (a == GuardValue::kRandom || b == GuardValue::kRandom)
    return GuardValue::kRandom;
  return GuardValue::kFalse;
}

GuardValue GuardNot(GuardValue a) {
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
