#pragma once

#include <memory>
#include <string>

#include "elaborator/annex_f_grammar.h"
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
// This file models the unclocked fragment of §F.5.3.1: the property forms whose
// neutral satisfaction §F.5.3.1 spells out directly, the unclocked top-level
// property T (a property, a disable iff guard, or a parenthesized T), and the
// disabling relation w |=^d T together with the pass/disabled/fail trichotomy.
// The clocked-property rule w |= Q iff w |= T^p(Q, 1) and the assertion-
// statement rules (which thread their operands through @(c) and the clocked
// top-level property U) are defined by §F.5.3.1 in terms of the §F.5.1.2
// property rewrite T^p; that rewrite is a separate subclause's machinery and is
// not modeled here.

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
  std::shared_ptr<const SequenceExpr> sequence;  // R for strong/weak/implication
  std::shared_ptr<const BooleanExpr> boolean;    // b for accept_on
  std::shared_ptr<const PropertyExpr> lhs;        // sub-property / first operand
  std::shared_ptr<const PropertyExpr> rhs;        // second operand
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
  std::shared_ptr<const TopLevelProperty> inner;          // T for ( T )
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
bool NeutrallySatisfiesTopLevel(const Word& word,
                                const TopLevelProperty& top);

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

}  // namespace delta
