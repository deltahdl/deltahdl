#pragma once

#include <memory>
#include <string>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_property_rewrite.h"
#include "elaborator/annex_f_tight_satisfaction.h"

namespace delta {

// §F.5.3.1 defines neutral satisfaction, the relation w |= P, for the
// properties, top-level properties, and assertion statements of the §F.3.2
// grammar, under the assumption that no local variables are involved. The
// relation is layered on §F.5.2's tight satisfaction of sequences (used by the
// strong/weak/implication forms) and on the §F.5 alphabet word operations
// (suffix w^{i.}, letterwise complement w-bar, finite prefixes, and the
// T^omega / _|_^omega tails).
//
// This file models §F.5.3.1 in two layers. The unclocked layer covers the
// property forms whose neutral satisfaction §F.5.3.1 spells out directly, the
// unclocked top-level property T (a property, a disable iff guard, or a
// parenthesized T), and the disabling relation w |=^d T together with the
// pass/disabled/fail trichotomy. The clocked layer covers the rule
// w |= Q iff w |= T^p(Q, 1), the clocked top-level property U, and the
// assertion-statement forms (always/initial x assert/assume/cover, threading
// their operands through @(c) and U). The clocked layer borrows the §F.5.1.2
// ClockedProperty model and its property rewrite T^p (a satisfied dependency):
// it routes every clocked property through T^p(., 1) -- or, for an explicit
// @(c), through T^p(., c) -- and then evaluates the resulting unclocked
// property with the layer above. A Boolean emitted by T^p in property position
// is read as the property strong(b).

// §F.3.2 production P, restricted to the unclocked forms §F.5.3.1 evaluates
// directly. strong(R) and weak(R) carry a sequence operand R; the implication
// (R |-> P) carries both a sequence antecedent and a property consequent;
// accept_on(b) P carries a Boolean abort condition.
struct PropertyExpr {
  enum class Kind {
    kStrong,       // strong ( R )
    kWeak,         // weak ( R )
    kParen,        // ( P )
    kNot,          // not P
    kImplication,  // ( R |-> P )
    kOr,           // ( P1 or P2 )
    kAnd,          // ( P1 and P2 )
    kNexttime,     // ( nexttime P )
    kUntil,        // ( P1 until P2 )
    kAcceptOn,     // ( accept_on ( b ) P )
  };

  Kind kind = Kind::kStrong;
  std::shared_ptr<const SequenceExpr>
      sequence;                                // R for strong/weak/implication
  std::shared_ptr<const BooleanExpr> boolean;  // b for accept_on
  std::shared_ptr<const PropertyExpr> lhs;     // sub-property / first operand
  std::shared_ptr<const PropertyExpr> rhs;     // second operand
};

std::shared_ptr<const PropertyExpr> PropStrong(
    std::shared_ptr<const SequenceExpr> r);
std::shared_ptr<const PropertyExpr> PropWeak(
    std::shared_ptr<const SequenceExpr> r);
std::shared_ptr<const PropertyExpr> PropParen(
    std::shared_ptr<const PropertyExpr> inner);
std::shared_ptr<const PropertyExpr> PropNot(
    std::shared_ptr<const PropertyExpr> inner);
std::shared_ptr<const PropertyExpr> PropImplication(
    std::shared_ptr<const SequenceExpr> antecedent,
    std::shared_ptr<const PropertyExpr> consequent);
std::shared_ptr<const PropertyExpr> PropOr(
    std::shared_ptr<const PropertyExpr> a,
    std::shared_ptr<const PropertyExpr> b);
std::shared_ptr<const PropertyExpr> PropAnd(
    std::shared_ptr<const PropertyExpr> a,
    std::shared_ptr<const PropertyExpr> b);
std::shared_ptr<const PropertyExpr> PropNexttime(
    std::shared_ptr<const PropertyExpr> inner);
std::shared_ptr<const PropertyExpr> PropUntil(
    std::shared_ptr<const PropertyExpr> a,
    std::shared_ptr<const PropertyExpr> b);
std::shared_ptr<const PropertyExpr> PropAcceptOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const PropertyExpr> inner);

// §F.3.2 production T (unclocked top-level property), in the unclocked forms
// §F.5.3.1 evaluates: a bare property P, a disable iff (b) P guard, and a
// parenthesized top-level property ( T ).
struct TopLevelProperty {
  enum class Kind {
    kProperty,    // P
    kDisableIff,  // disable iff ( b ) P
    kParen,       // ( T )
  };

  Kind kind = Kind::kProperty;
  std::shared_ptr<const BooleanExpr> disable_condition;  // b for disable iff
  std::shared_ptr<const PropertyExpr> property;          // P
  std::shared_ptr<const TopLevelProperty> inner;         // T for ( T )
};

std::shared_ptr<const TopLevelProperty> TopProperty(
    std::shared_ptr<const PropertyExpr> p);
std::shared_ptr<const TopLevelProperty> TopDisableIff(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const PropertyExpr> p);
std::shared_ptr<const TopLevelProperty> TopParen(
    std::shared_ptr<const TopLevelProperty> inner);

// §F.5.3.1: neutral satisfaction w |= P of a property by a nonempty word w.
bool NeutrallySatisfies(const Word& word, const PropertyExpr& property);

// §F.5.3.1: neutral satisfaction w |= T of an (unclocked) top-level property.
bool NeutrallySatisfiesTopLevel(const Word& word, const TopLevelProperty& top);

// §F.5.3.1: the disabling relation w |=^d T for an (unclocked) top-level
// property. A bare property is never disabled; a disable iff guard is disabled
// when its condition first becomes true on a word for which the guarded
// property is true under a T^omega completion but not under a _|_^omega one.
bool DisablesTopLevel(const Word& word, const TopLevelProperty& top);

// §F.5.3.1: "T is said to pass on w if w |= T", "T is said to be disabled on w
// if w |=^d T", and "T is said to fail on w if T neither passes nor is disabled
// on w." The standard notes pass and disabled are mutually exclusive.
bool PassesTopLevel(const Word& word, const TopLevelProperty& top);
bool IsDisabledTopLevel(const Word& word, const TopLevelProperty& top);
bool FailsTopLevel(const Word& word, const TopLevelProperty& top);

// §F.5.3.1: neutral satisfaction of a clocked property Q, defined by the single
// rule w |= Q iff w |= T^p(Q, 1). Q is the §F.5.1.2 ClockedProperty; the clock
// is pushed down by that subclause's property rewrite under the constant clock
// 1 and the unclocked result is evaluated as a §F.5.3.1 property.
bool NeutrallySatisfiesClockedProperty(const Word& word,
                                       const ClockedProperty& q);

// §F.3.2 production U (clocked top-level property), in the forms §F.5.3.1
// evaluates: a clocked property Q, a disable iff (b) Q guard, and a
// parenthesized clocked top-level property ( U ).
struct ClockedTopLevelProperty {
  enum class Kind {
    kProperty,    // Q
    kDisableIff,  // disable iff ( b ) Q
    kParen,       // ( U )
  };

  Kind kind = Kind::kProperty;
  std::shared_ptr<const BooleanExpr> disable_condition;  // b for disable iff
  std::shared_ptr<const ClockedProperty> property;       // Q
  std::shared_ptr<const ClockedTopLevelProperty> inner;  // U for ( U )
};

std::shared_ptr<const ClockedTopLevelProperty> ClockedTopProperty(
    std::shared_ptr<const ClockedProperty> q);
std::shared_ptr<const ClockedTopLevelProperty> ClockedTopDisableIff(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const ClockedProperty> q);
std::shared_ptr<const ClockedTopLevelProperty> ClockedTopParen(
    std::shared_ptr<const ClockedTopLevelProperty> inner);

// §F.5.3.1: neutral satisfaction w |= U and disabling w |=^d U of a clocked
// top-level property. The U forms mirror the unclocked T forms with Q replacing
// P, so each reduces to its T counterpart over the unclocked property T^p(Q,
// 1).
bool NeutrallySatisfiesTopLevelClocked(const Word& word,
                                       const ClockedTopLevelProperty& top);
bool DisablesTopLevelClocked(const Word& word,
                             const ClockedTopLevelProperty& top);

// §F.5.3.1: the pass/disabled/fail trichotomy applies to clocked top-level
// properties as well, since the disabling-of-top-level definitions it follows
// cover both T and U.
bool PassesTopLevelClocked(const Word& word,
                           const ClockedTopLevelProperty& top);
bool IsDisabledTopLevelClocked(const Word& word,
                               const ClockedTopLevelProperty& top);
bool FailsTopLevelClocked(const Word& word, const ClockedTopLevelProperty& top);

// §F.3.2 production A (assertion statement) in the forms §F.5.3.1 defines
// neutral satisfaction for. Each statement combines an activation (always or
// initial), a role (assert, assume, or cover), and a clocked top-level body.
// The body comes in two shapes: an explicit leading clock over an unclocked
// top-level property, @( c ) T, or an intrinsically clocked top-level property
// U.
struct AssertionStatement {
  enum class Activation { kAlways, kInitial };
  enum class Role { kAssert, kAssume, kCover };
  enum class Form {
    kExplicitClock,  // @( c ) T
    kClockedTop,     // U
  };

  Activation activation = Activation::kAlways;
  Role role = Role::kAssert;
  Form form = Form::kExplicitClock;
  std::shared_ptr<const BooleanExpr> clock;     // c, for kExplicitClock
  std::shared_ptr<const TopLevelProperty> top;  // T, for kExplicitClock
  std::shared_ptr<const ClockedTopLevelProperty> clocked_top;  // U, kClockedTop
};

std::shared_ptr<const AssertionStatement> AssertionWithClock(
    AssertionStatement::Activation activation, AssertionStatement::Role role,
    std::shared_ptr<const BooleanExpr> clock,
    std::shared_ptr<const TopLevelProperty> top);
std::shared_ptr<const AssertionStatement> AssertionWithClockedTop(
    AssertionStatement::Activation activation, AssertionStatement::Role role,
    std::shared_ptr<const ClockedTopLevelProperty> clocked_top);

// §F.5.3.1: neutral satisfaction w, b |= A of an assertion statement, where b
// is the Boolean enabling condition (1 for a declarative assertion statement).
// The always forms quantify over every index; the initial forms over the first
// clocked activation. An assert or assume statement requires that the body pass
// or be disabled at every enabled activation; a cover statement requires that
// it pass at some enabled activation.
bool NeutrallySatisfiesAssertion(const Word& word, const BooleanExpr& enabling,
                                 const AssertionStatement& assertion);

// §F.5.3.1: an assertion statement together with the enabling condition under
// which it is evaluated, so a set of assumptions can be carried as a list.
struct EnabledAssertion {
  AssertionStatement statement;
  std::shared_ptr<const BooleanExpr> enabling;
};

// §F.5.3.1: "A word in the set of words is feasible if every assumption in the
// set of assumptions is satisfied on the word."
bool WordIsFeasible(const Word& word,
                    const std::vector<EnabledAssertion>& assumptions);

// §F.5.3.1: "An assert property statement is satisfied on a set of words
// predicated on the set of assumptions if it is satisfied on each feasible
// word."
bool AssertSatisfiedOnWordSet(const EnabledAssertion& assertion,
                              const std::vector<Word>& words,
                              const std::vector<EnabledAssertion>& assumptions);

// §F.5.3.1: "A cover property statement is satisfied on a set of words
// predicated on the set of assumptions if it is satisfied on at least one
// feasible word."
bool CoverSatisfiedOnWordSet(const EnabledAssertion& assertion,
                             const std::vector<Word>& words,
                             const std::vector<EnabledAssertion>& assumptions);

// §F.5.3.1: "An assertion statement holds globally on the set of words
// predicated on the set of assumptions if it is satisfied on every feasible
// word."
bool HoldsGloballyOnWordSet(const EnabledAssertion& assertion,
                            const std::vector<Word>& words,
                            const std::vector<EnabledAssertion>& assumptions);

}  // namespace delta
