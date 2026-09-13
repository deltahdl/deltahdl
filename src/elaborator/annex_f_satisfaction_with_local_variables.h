#pragma once

#include <memory>

#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables.h"

namespace delta {

// §F.5.6 is the heading under which neutral satisfaction (§F.5.6.1), weak and
// strong satisfaction by finite words (§F.5.6.2) and vacuity (§F.5.6.3) are
// defined with local variables, each stating that its rules are those of the
// §F.5.3 notion of the same name with the understanding that the underlying
// properties may carry local variables. What the title adds to §F.5.3's scope
// is the local variable context: each relation of §F.5.6 is over a word and a
// context L_0 where §F.5.3's is over the word alone, §F.5.6.1 enters from the
// empty context, and the context is read and written by the local variable
// forms alone. This file models the scope from the §F.5.6 side, as
// annex_f_satisfaction_without_local_variables.h does from §F.5.3's: a
// predicate saying whether a property or top-level property of the §F.5.6
// model involves a local variable, and so lies outside §F.5.3; and the
// retraction of §F.5.3's embedding, defined on the fragment that involves
// none, under which the relations of §F.5.6 are observed to agree with those
// of §F.5.3 under every context, while outside the fragment they hold of
// properties §F.5.3 has no counterpart for.

// §F.5.6: a property of the §F.5.6 model involves a local variable iff a
// declaration form ( t v ; P ) occurs in it at any depth or one of its
// sequence operands involves one by the §F.5.3 predicate; a top-level property
// iff its declaration form ( t v ; T ) occurs or its property involves one.
bool LvPropertyInvolvesLocalVariables(const LvProperty& property);
bool LvTopLevelPropertyInvolvesLocalVariables(const LvTopLevelProperty& top);

// §F.5.3 is the fragment of §F.5.6 without local variables, and on it the
// embedding AsPropertyWithLocalVariables has an inverse: the §F.5.6 property
// or top-level property that involves no local variable is the §F.5.3 one of
// the same shape, with every operator, operand and Boolean kept. Outside the
// fragment there is no such property, and the result is null.
std::shared_ptr<const PropertyExpr> AsPropertyWithoutLocalVariables(
    const LvProperty& property);
std::shared_ptr<const TopLevelProperty> AsTopLevelPropertyWithoutLocalVariables(
    const LvTopLevelProperty& top);

}  // namespace delta
