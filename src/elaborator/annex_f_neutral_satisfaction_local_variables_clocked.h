#pragma once

#include <cstdint>
#include <memory>
#include <string>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_neutral_satisfaction_local_variables.h"
#include "elaborator/annex_f_property_rewrite.h"
#include "elaborator/annex_f_tight_satisfaction.h"
#include "elaborator/annex_f_tight_satisfaction_local_variables.h"

namespace delta {

// §F.5.6.1's clocked column, the rules the unclocked layer of
// annex_f_neutral_satisfaction_local_variables.h leaves out: w, L_0 |= Q iff
// w, L_0 |= T^p(Q, 1); the clocked top-level property U, whose forms mirror
// T's with Q for P and whose declaration form ( t v ; U ) strips its name
// from the context as ( t v ; T ) does; the disabling relation w, L_0 |=^d U
// and the pass, disabled and fail verdicts over it; and the assertion
// statement, whose rules the subclause has identical to §F.5.3.1's with the
// understanding that the underlying properties can have local variables. The
// clocked property Q of §F.5.1.2's model carries no declaration form, T^p
// having no rule for one, but its sequences may declare and sample local
// variables, which T^s of §F.5.1.1 keeps under the clock, so every relation
// here is observable through them: a sampling under a clock is met at a tick,
// and a name declared at the top level is hidden from the body under any
// context. Each relation reduces its input to the §F.5.6.1 unclocked model
// through T^p(., c), read into the property model and embedded with local
// variables, and is decided there.

// §F.5.6.1: w, L_0 |= Q iff w, L_0 |= T^p(Q, 1).
bool NeutrallySatisfiesClockedPropertyWithLocals(const Word& word,
                                                 const ClockedProperty& q,
                                                 const LocalContext& context);

// §F.3.2 production U with local variables: a clocked property Q, a disable
// iff (b) Q guard, a parenthesized ( U ) and the declaration ( t v ; U ).
struct LvClockedTopLevelProperty {
  enum class Kind : std::uint8_t {
    kProperty,      // Q
    kDisableIff,    // disable iff ( b ) Q
    kParen,         // ( U )
    kLocalVarDecl,  // ( t v ; U )
  };

  Kind kind = Kind::kProperty;
  std::shared_ptr<const BooleanExpr> disable_condition;    // b for disable iff
  std::shared_ptr<const ClockedProperty> property;         // Q
  std::shared_ptr<const LvClockedTopLevelProperty> inner;  // U, paren or decl
  std::string local_var_type;                              // t, for declaration
  std::string local_var_name;                              // v, for declaration
};

std::shared_ptr<const LvClockedTopLevelProperty> LvClockedTopProperty(
    std::shared_ptr<const ClockedProperty> q);
std::shared_ptr<const LvClockedTopLevelProperty> LvClockedTopDisableIff(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const ClockedProperty> q);
std::shared_ptr<const LvClockedTopLevelProperty> LvClockedTopParen(
    std::shared_ptr<const LvClockedTopLevelProperty> inner);
std::shared_ptr<const LvClockedTopLevelProperty> LvClockedTopLocalVarDecl(
    std::string type, std::string name,
    std::shared_ptr<const LvClockedTopLevelProperty> body);

// §F.5.6.1: the unclocked top-level property with local variables that
// decides U under the clock c -- 1 for U standing alone, the clock of @( c ) T
// for a T given as the U whose properties carry no clock form, as §F.5.3.1
// lifts P into Q. Each form mirrors its T counterpart with T^p(Q, c) for P;
// the declaration and the parenthesis carry through.
std::shared_ptr<const LvTopLevelProperty> UnclockTopLevelWithLocals(
    const LvClockedTopLevelProperty& top,
    const std::shared_ptr<const BooleanExpr>& clock);

// §F.5.6.1: neutral satisfaction w, L_0 |= U, disabling w, L_0 |=^d U, and
// the pass, disabled and fail verdicts, which the subclause states for U as
// for T.
bool NeutrallySatisfiesTopLevelClockedWithLocals(
    const Word& word, const LvClockedTopLevelProperty& top,
    const LocalContext& context);
bool DisablesTopLevelClockedWithLocals(const Word& word,
                                       const LvClockedTopLevelProperty& top,
                                       const LocalContext& context);
bool PassesTopLevelClockedWithLocals(const Word& word,
                                     const LvClockedTopLevelProperty& top,
                                     const LocalContext& context);
bool IsDisabledTopLevelClockedWithLocals(const Word& word,
                                         const LvClockedTopLevelProperty& top,
                                         const LocalContext& context);
bool FailsTopLevelClockedWithLocals(const Word& word,
                                    const LvClockedTopLevelProperty& top,
                                    const LocalContext& context);

// §F.3.2 production A with local variables, in the shapes of §F.5.3.1's
// AssertionStatement: an activation, a role and a body, which is @( c ) T for
// the explicit clock form and U otherwise, both given as an
// LvClockedTopLevelProperty since a T is the U whose properties carry no clock
// form.
struct LvAssertionStatement {
  AssertionStatement::Activation activation =
      AssertionStatement::Activation::kAlways;
  AssertionStatement::Role role = AssertionStatement::Role::kAssert;
  AssertionStatement::Form form = AssertionStatement::Form::kExplicitClock;
  std::shared_ptr<const BooleanExpr> clock;               // c, kExplicitClock
  std::shared_ptr<const LvClockedTopLevelProperty> body;  // T or U
};

std::shared_ptr<const LvAssertionStatement> LvAssertionWithClock(
    AssertionStatement::Activation activation, AssertionStatement::Role role,
    std::shared_ptr<const BooleanExpr> clock,
    std::shared_ptr<const LvClockedTopLevelProperty> top);
std::shared_ptr<const LvAssertionStatement> LvAssertionWithClockedTop(
    AssertionStatement::Activation activation, AssertionStatement::Role role,
    std::shared_ptr<const LvClockedTopLevelProperty> clocked_top);

// §F.5.6.1: neutral satisfaction w, b |= A of an assertion statement whose
// body may carry local variables, by the rules of §F.5.3.1: the activation
// points are those of §F.5.3.1's ActivationPointEnabled under the enabling
// condition b, and at each the body is decided from the empty context, as
// w |= Q iff w, {} |= Q has it, an assert or assume statement requiring that
// it not fail at every enabled point and a cover statement that it pass at
// some.
bool NeutrallySatisfiesAssertionWithLocals(
    const Word& word, const BooleanExpr& enabling,
    const LvAssertionStatement& assertion);

}  // namespace delta
