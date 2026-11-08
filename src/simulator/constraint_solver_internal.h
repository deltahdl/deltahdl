#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
#include <random>
#include <string>
#include <unordered_map>
#include <vector>

#include "simulator/constraint_solver.h"

namespace delta {

int64_t DrawUniformInRange(bool is_signed, int64_t lo, int64_t hi,
                           std::mt19937& rng);

RandVariable Narrowed(const RandVariable& var, const ConstraintExpr& sub);
bool IsComparison(ConstraintKind kind);
ConstraintKind MirrorComparisonKind(ConstraintKind kind);

void ApplyConcreteConstraint(const ConstraintExpr& c,
                             std::unordered_map<std::string, int64_t>& values,
                             std::mt19937& rng, bool holds_state_value);

void CollectConstraints(const std::vector<ConstraintBlock>& blocks,
                        const std::vector<ConstraintExpr>& extra,
                        std::vector<const ConstraintExpr*>& hard,
                        std::vector<const ConstraintExpr*>& soft);

void SeedInactiveVariables(
    std::unordered_map<std::string, RandVariable>& variables,
    std::unordered_map<std::string, int64_t>& values,
    std::unordered_map<std::string, double>& real_values);

void DrawArraySizeVariables(
    std::unordered_map<std::string, RandVariable>& variables,
    std::unordered_map<std::string, int64_t>& values,
    const std::function<int64_t(RandVariable&)>& gen);

bool ConfinedTo(const ConstraintExpr& c, const std::string& name);

size_t ClampCountToSize(size_t count, const std::string& size_var,
                        const std::unordered_map<std::string, int64_t>& values);

}  // namespace delta
