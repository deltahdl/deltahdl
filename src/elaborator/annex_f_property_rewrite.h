#pragma once

#include <memory>

#include "elaborator/annex_f_grammar.h"

namespace delta {

// §F.5.1.2 defines the transformation T^p(p, c): given a property and a clock
// c, it produces an equivalent unclocked property by pushing the clock down to
// every operand. It is the property-level companion of the sequence rewrite
// T^s (§F.5.1.1) and delegates to it for the sequence operands of the
// strong/weak/implication forms.
//
// The §F.3.2 clocked property Q differs from the unclocked property P only by
// the clock form @( b ) P and the synchronous abort sync_accept_on; the
// neutral-satisfaction model of §F.5.3.1 deliberately leaves those clocked
// forms out and defers them to this subclause. So this file carries its own
// property model -- the domain and codomain of T^p -- covering exactly the
// twelve forms §F.5.1.2 rewrites, plus a Boolean-as-property leaf because the
// nexttime and until rules emit the clock c in property position.
struct ClockedProperty {
  enum class Kind {
    kBoolean,        // b, a Boolean used as a property (e.g. the emitted !c)
    kStrong,         // strong ( R )
    kWeak,           // weak ( R )
    kClock,          // @( b ) P
    kDisableIff,     // disable iff ( b ) P
    kAcceptOn,       // accept_on ( b ) P
    kSyncAcceptOn,   // sync_accept_on ( b ) P
    kNot,            // not P
    kImplication,    // ( R |-> P )
    kOr,             // ( P1 or P2 )
    kAnd,            // ( P1 and P2 )
    kNexttime,       // ( nexttime P )
    kUntil,          // ( P1 until P2 )
  };

  Kind kind = Kind::kBoolean;
  std::shared_ptr<const BooleanExpr> boolean;     // b for Boolean/clock/abort
  std::shared_ptr<const SequenceExpr> sequence;   // R for strong/weak/impl
  std::shared_ptr<const ClockedProperty> lhs;     // sub-property / consequent
  std::shared_ptr<const ClockedProperty> rhs;     // second operand
};

// Factories for each form. Named with a Clk prefix to stay distinct from the
// §F.5.3.1 PropertyExpr constructors that share the delta namespace.
std::shared_ptr<const ClockedProperty> ClkBoolean(
    std::shared_ptr<const BooleanExpr> b);
std::shared_ptr<const ClockedProperty> ClkStrong(
    std::shared_ptr<const SequenceExpr> r);
std::shared_ptr<const ClockedProperty> ClkWeak(
    std::shared_ptr<const SequenceExpr> r);
std::shared_ptr<const ClockedProperty> ClkClock(
    std::shared_ptr<const BooleanExpr> clock,
    std::shared_ptr<const ClockedProperty> p);
std::shared_ptr<const ClockedProperty> ClkDisableIff(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const ClockedProperty> p);
std::shared_ptr<const ClockedProperty> ClkAcceptOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const ClockedProperty> p);
std::shared_ptr<const ClockedProperty> ClkSyncAcceptOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const ClockedProperty> p);
std::shared_ptr<const ClockedProperty> ClkNot(
    std::shared_ptr<const ClockedProperty> p);
std::shared_ptr<const ClockedProperty> ClkImplication(
    std::shared_ptr<const SequenceExpr> antecedent,
    std::shared_ptr<const ClockedProperty> consequent);
std::shared_ptr<const ClockedProperty> ClkOr(
    std::shared_ptr<const ClockedProperty> a,
    std::shared_ptr<const ClockedProperty> b);
std::shared_ptr<const ClockedProperty> ClkAnd(
    std::shared_ptr<const ClockedProperty> a,
    std::shared_ptr<const ClockedProperty> b);
std::shared_ptr<const ClockedProperty> ClkNexttime(
    std::shared_ptr<const ClockedProperty> p);
std::shared_ptr<const ClockedProperty> ClkUntil(
    std::shared_ptr<const ClockedProperty> a,
    std::shared_ptr<const ClockedProperty> b);

bool ClockedPropertyEqual(const ClockedProperty& lhs,
                          const ClockedProperty& rhs);

// §F.5.1.2: the transformation T^p(p, c). `clock` is the Boolean c. The result
// contains no clock, sync_accept_on, nexttime, or until-over-clock forms beyond
// the level-sensitive shapes the rules emit, so it is an unclocked property.
std::shared_ptr<const ClockedProperty> RewritePropertyUnderClock(
    const ClockedProperty& property, std::shared_ptr<const BooleanExpr> clock);

}  // namespace delta
