#include <cstdint>
#include <functional>
#include <initializer_list>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include "simulator/constraint_solver.h"

namespace delta {

namespace {

using TrialValues = std::unordered_map<std::string, int64_t>;

TrialValues ValuesInScope(const TrialValues& vals, const std::string& prefix) {
  TrialValues local;
  for (const auto& [name, value] : vals) {
    if (name.starts_with(prefix))
      local.emplace(name.substr(prefix.size()), value);
  }
  return local;
}

void ScopeName(std::string& name, const std::string& prefix) {
  if (!name.empty()) name = prefix + name;
}

void ScopeNames(std::vector<std::string>& names, const std::string& prefix) {
  for (auto& name : names) ScopeName(name, prefix);
}

template <typename Result>
void ScopeCallback(std::function<Result(const TrialValues&)>& fn,
                   const std::string& prefix) {
  if (!fn) return;
  fn = [unscoped = std::move(fn), prefix](const TrialValues& vals) {
    return unscoped(ValuesInScope(vals, prefix));
  };
}

void ScopeGuard(GuardPredicate& guard, const std::string& prefix) {
  ScopeCallback(guard.leaf_fn, prefix);
  for (auto& operand : guard.operands) ScopeGuard(operand, prefix);
}

void ScopeConstraint(ConstraintExpr& ce, const std::string& prefix) {
  for (std::string* name :
       {&ce.var_name, &ce.cond_var, &ce.size_var, &ce.co_var_name}) {
    ScopeName(*name, prefix);
  }
  for (auto* names : {&ce.unique_vars, &ce.reduce_vars, &ce.ref_vars})
    ScopeNames(*names, prefix);
  for (auto& sub : ce.sub_constraints) ScopeConstraint(sub, prefix);
  for (auto& sub : ce.else_constraints) ScopeConstraint(sub, prefix);
  if (ce.inner != nullptr) ScopeConstraint(*ce.inner, prefix);
  ScopeCallback(ce.cond_fn, prefix);
  ScopeCallback(ce.eval_fn, prefix);
  ScopeCallback(ce.derive_fn, prefix);
  ScopeGuard(ce.guard, prefix);
}

}  // namespace

void ConstraintSolver::SetNameScope(std::string prefix) {
  name_scope_ = std::move(prefix);
}

void ConstraintSolver::AddVariable(const RandVariable& var) {
  RandVariable& added = variables_[name_scope_ + var.name];
  added = var;
  added.name = name_scope_ + var.name;
}

void ConstraintSolver::AddConstraintBlock(const ConstraintBlock& block) {
  blocks_.push_back(block);
  if (name_scope_.empty()) return;
  ConstraintBlock& added = blocks_.back();
  ScopeName(added.name, name_scope_);
  for (auto& ce : added.constraints) ScopeConstraint(ce, name_scope_);
}

void ConstraintSolver::AddSolveBefore(const std::vector<std::string>& before,
                                      const std::vector<std::string>& after) {
  for (const auto& b : before) {
    for (const auto& a : after) {
      solve_before_edges_.emplace_back(name_scope_ + b, name_scope_ + a);
    }
  }
}

void ConstraintSolver::AddFunctionArgPriority(
    const std::vector<std::string>& higher,
    const std::vector<std::string>& lower) {
  for (const auto& h : higher) {
    for (const auto& l : lower) {
      function_arg_priority_edges_.emplace_back(name_scope_ + h,
                                                name_scope_ + l);
    }
  }
}

}  // namespace delta
