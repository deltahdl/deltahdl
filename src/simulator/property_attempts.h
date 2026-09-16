#pragma once

#include <cstdint>
#include <functional>
#include <vector>

#include "common/arena.h"
#include "parser/ast_stmt.h"

namespace delta {

class SimContext;

// §16.12: the attempts in flight of one concurrent assertion whose property
// is a tree of operands under not, or and and (§16.12.3 to §16.12.5), each
// attempt begun at one tick of the assertion's clock and holding the state
// of every operand: a boolean's value at the tick, a sequence's attempt.
struct PropertyTreeState;

// The state of one assertion statement's tree, its sequence operands
// flattened; nullptr where an operand's sequence is not one the monitor
// reads.
PropertyTreeState* CreatePropertyTreeState(const PropertyExprNode* root,
                                           SimContext& ctx, Arena& arena);

// One tick: every attempt in flight advances and a new one begins, and each
// whose tree is decided at this tick reaches its verdict, true or false, and
// leaves; `disabled` drops every attempt in flight and begins none. The
// sampled value functions the tree holds are sampled at the tick first.
std::vector<bool> AdvancePropertyTree(PropertyTreeState& state, bool disabled,
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
std::vector<bool> FinishPropertyTree(PropertyTreeState& state);

}  // namespace delta
