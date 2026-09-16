#pragma once

#include <vector>

#include "common/arena.h"
#include "parser/ast.h"
#include "parser/expr_substitute.h"

namespace delta {

class PropertyRegistry;

// §16.12.1 and §16.13.4: what an instance of a named property or sequence,
// written as a name or a call, gives the assertion that stands it as its
// property_spec, whether the statement stands outside procedural code
// (elaborator_items_assertions.cpp) or inside it (§16.14.6,
// procedural_concurrent_assertion.cpp).

// §16.12.18: whether an actual argument of `instance` is a sequence_expr or
// a property_expr, which the boolean substitution does not read, so the
// instance is evaluated as the body's tree.
bool InstanceHasTreeActual(const Expr* instance);

// §16.12.18 by way of §16.8.1: one event of the instantiated property's
// clock with the actuals in the formals' places.
EventExpr SubstituteClockEvent(EventExpr ev, const ActualsByFormal& actuals,
                               Arena& arena);

// The declaration `operand` instantiates where it names one of `kind`, an
// identifier or a call naming a sequence or a property; nullptr otherwise.
const ModuleItem* InstantiatedDecl(const Expr* operand, ModuleItemKind kind,
                                   const PropertyRegistry& registry);

// §16.12.2 and §16.13.4: a sequence declaration of one operand, an instance
// of the named sequence `instance` names, for the flattening to expand.
ModuleItem* SequenceInstanceBody(Expr* instance, Arena& arena);

// §16.13.3 and §16.13.4: the clock flowing into a property declared with
// none, from the clocking event its body opens with or the clock of the
// sequence it opens with; empty otherwise.
const std::vector<EventExpr>& FlowedBodyClock(const ModuleItem* decl,
                                              const PropertyRegistry& registry);

// §16.13.4: a boolean operand of the tree that is the bare name of a named
// sequence, or a call of one, which the parser read as a boolean since a
// variable's name reads the same, is the sequence, a node the flattening
// expands; the walk reaches the trees an instance's actuals carry too.
void PromoteSequenceInstances(PropertyExprNode* node,
                              const PropertyRegistry& registry, Arena& arena);

}  // namespace delta
