#pragma once

#include <cstdint>
#include <functional>
#include <vector>

#include "common/arena.h"
#include "parser/ast_stmt.h"
#include "simulator/instance_bindings.h"

namespace delta {

class SimContext;

// §16.12: the attempts in flight of one concurrent assertion whose property
// is a tree of operands under not, or and and (§16.12.3 to §16.12.5), each
// attempt begun at one tick of the assertion's clock and holding the state
// of every operand: a boolean's value at the tick, a sequence's attempt.
struct PropertyTreeState;

// The state of one assertion statement's tree, its sequence operands
// flattened; nullptr where an operand's sequence is not one the monitor
// reads. §16.13: `leading_clock` is the assertion's clocking event, on
// which every attempt begins, the clocks its sequences name beside being
// told apart from it by watchers on their signals.
PropertyTreeState* CreatePropertyTreeState(
    const PropertyExprNode* root, const std::vector<EventExpr>& leading_clock,
    SimContext& ctx, Arena& arena);

// The verdict of one attempt: whether the property held, and, where it did,
// whether because of vacuity, which §16.14.3 counts apart: an implication
// whose antecedent had no match, an if without else whose condition was
// false or a case selecting no item, at the root of the tree.
struct PropertyVerdict {
  bool holds = false;
  bool vacuous = false;
  // §16.14.6.1: the values the instance the attempt was saved when it was
  // queued, for its action block to read; nullptr for a static assertion's.
  const InstanceBindings* bindings = nullptr;
};

// One tick: every attempt in flight advances and one new one begins per
// entry of `instances`, one entry, null, for a static assertion and,
// §16.14.6, the saved values of each matured instance of a procedural one,
// and each whose tree is decided at this tick reaches its verdict and
// leaves; `disabled` drops every attempt in flight and begins none, though
// `attempted` counts those that would have begun, disabled or not, at a
// tick of the leading clock, as §16.14.3 counts attempts. The sampled value
// functions the tree holds are sampled at the tick first.
struct PropertyTick {
  uint32_t attempted = 0;
  std::vector<PropertyVerdict> verdicts;
};

using AttemptInstances = std::vector<const InstanceBindings*>;

PropertyTick AdvancePropertyTree(PropertyTreeState& state, bool disabled,
                                 const AttemptInstances& instances,
                                 SimContext& ctx, Arena& arena);

// §16.12.17: the declaration `instance` names where it is an instance,
// written as a name or a call, of a named property whose body the tree
// evaluator reads; nullptr for any other expression.
const ModuleItem* InstantiatedProperty(const Expr* instance, SimContext& ctx);

// §16.12.18: the sequence_expr or property_expr each actual argument of
// `instance` that is one carries, handed to `fn` in turn.
void ForEachPropertyActual(
    const Expr* instance,
    const std::function<void(const PropertyExprNode*)>& fn);

// The end of the run: each attempt still in flight is decided with its
// sequence operands still in flight read as §16.12.2 has them, a strong one
// false and a weak one true, and reaches its verdict.
std::vector<PropertyVerdict> FinishPropertyTree(PropertyTreeState& state);

}  // namespace delta
