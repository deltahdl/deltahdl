#pragma once

#include <cstddef>
#include <cstdint>
#include <functional>
#include <vector>

#include "common/arena.h"
#include "parser/ast_stmt.h"
#include "simulator/instance_bindings.h"

namespace delta {

class SimContext;

struct PropertyTreeState;

PropertyTreeState* CreatePropertyTreeState(
    const PropertyExprNode* root, const std::vector<EventExpr>& leading_clock,
    bool every_match, SimContext& ctx, Arena& arena);

struct PropertyVerdict {
  bool holds = false;
  bool vacuous = false;
  const InstanceBindings* bindings = nullptr;
  uint64_t started = 0;
  const Expr* failed_at = nullptr;
};

struct PropertyTick {
  uint32_t attempted = 0;
  std::vector<PropertyVerdict> verdicts;
  std::vector<uint64_t> disabled;
};

using AttemptInstances = std::vector<const InstanceBindings*>;

PropertyTick AdvancePropertyTree(PropertyTreeState& state, bool disabled,
                                 const AttemptInstances& instances,
                                 SimContext& ctx, Arena& arena);

const ModuleItem* InstantiatedProperty(const Expr* instance, SimContext& ctx);

void ForEachPropertyActual(
    const Expr* instance,
    const std::function<void(const PropertyExprNode*)>& fn);

void ReadPlainSequencesAsStrong(PropertyTreeState& state);

std::vector<PropertyVerdict> FinishPropertyTree(PropertyTreeState& state);

std::size_t AbortPropertyTreeAttempts(PropertyTreeState& state);

std::size_t AbortPropertyTreeAttemptAt(PropertyTreeState& state,
                                       uint64_t started);

}  // namespace delta
