#pragma once

#include <memory>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables.h"
#include "elaborator/annex_f_property_rewrite.h"

namespace delta {

// §F.5.3 is the heading under which neutral satisfaction (§F.5.3.1), weak and
// strong satisfaction by finite words (§F.5.3.2) and vacuity (§F.5.3.3) are
// defined, and its title states the one thing those three share: they are
// satisfaction without local variables. §F.5.3.1 opens by assuming that no
// property, sequence or unclocked property fragment involves a local variable,
// and §F.5.6 gives the same three notions with local variables, each stating
// that its rules are those of §F.5.3 with the understanding that the underlying
// properties may carry local variables. So §F.5.3 is the fragment of §F.5.6 in
// which nothing does, and this file models that scope: a predicate saying
// whether a sequence, property, top-level property or assertion statement of
// the §F.3.2 grammar involves a local variable, and the embedding of a §F.5.3
// property into the §F.5.6 property model, under which the two subclauses'
// relations are observed to agree on every input in §F.5.3's scope.

// §F.5.3: a sequence involves a local variable iff a local variable
// declaration ( t v [ = e ]; R ) or sampling ( 1, v = e ) form of §F.3.2 occurs
// in it at any depth.
bool SequenceInvolvesLocalVariables(const SequenceExpr& sequence);

// §F.5.3: the §F.3.2 property productions carry no local variable form of
// their own, so a property, top-level property or clocked property involves a
// local variable iff one of its sequence operands does, at any depth.
bool PropertyInvolvesLocalVariables(const PropertyExpr& property);
bool TopLevelPropertyInvolvesLocalVariables(const TopLevelProperty& top);
bool ClockedPropertyInvolvesLocalVariables(const ClockedProperty& property);
bool ClockedTopLevelPropertyInvolvesLocalVariables(
    const ClockedTopLevelProperty& top);

// §F.5.3: an assertion statement involves a local variable iff its body does,
// whichever of the two §F.3.2 shapes -- @( c ) T or U -- the body takes.
bool AssertionInvolvesLocalVariables(const AssertionStatement& assertion);

// §F.5.3 is the fragment of §F.5.6 without local variables: a §F.5.3 property
// or top-level property is the §F.5.6 one of the same shape, which has a local
// variable declaration form the §F.5.3 model lacks and never needs here. The
// embedding keeps every operator and operand and adds no declaration, so that
// §F.5.6's relations, entered from the empty context, can be put beside
// §F.5.3's on the same input.
std::shared_ptr<const LvProperty> AsPropertyWithLocalVariables(
    const PropertyExpr& property);
std::shared_ptr<const LvTopLevelProperty> AsTopLevelPropertyWithLocalVariables(
    const TopLevelProperty& top);

}  // namespace delta
