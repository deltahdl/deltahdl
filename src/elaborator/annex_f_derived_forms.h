#pragma once

#include <cstdint>
#include <memory>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"

namespace delta {

// §F.3.4 lists the derived forms of Annex F: the shapes the concrete syntax
// writes, each defined as a composition of the §F.3.2 primitives, so that the
// satisfaction relations of §F.5 need only be stated for the primitives. This
// file holds the derived forms as functions from a concrete shape to the
// primitive form it stands for.

// §16.14's four concurrent assertion directives, where §F.3.2's assertion
// production A has three roles.
enum class ConcurrentAssertionDirective : std::uint8_t {
  kAssert,
  kAssume,
  kCover,
  kRestrict,
};

// §F.3.4.1: restrict property is defined as assume property, so the role a
// restrict statement takes in the §F.3.2 grammar is the assume role, and each
// of the other three directives is its own role. §16.14.4 says the same from
// the language's side, that a restrict property statement has the semantics of
// an assume property statement, and what sets it apart there -- that it is not
// verified in simulation and has no action block -- is nothing the
// satisfaction of a word sees.
AssertionStatement::Role RoleOfConcurrentAssertionDirective(
    ConcurrentAssertionDirective directive);

// §F.3.4.2.1: the derived consecutive repetition operators, each built from
// the two §F.3.2 primitives R[*0] and R[*1:$] with ##1 and or. The four below
// are the concrete shapes §16.9.2 writes, and each is the tree §F.3.4.2.1's
// identities unfold it to, so a word tightly satisfies the derived form iff it
// satisfies that tree under §F.5.2.

// R[*m]: R[*0] for m = 0, and (R[*m-1] ##1 R) for m > 0.
std::shared_ptr<const SequenceExpr> SeqRepeatExactly(
    std::shared_ptr<const SequenceExpr> r, unsigned int m);

// R[*m:n] for m <= n: R[*m] where the bounds meet, and (R[*m:n-1] or R[*n])
// where they differ.
std::shared_ptr<const SequenceExpr> SeqRepeatRange(
    std::shared_ptr<const SequenceExpr> r, unsigned int m, unsigned int n);

// R[*m:$]: (R[*0] or R[*1:$]) for m = 0, the primitive R[*1:$] for m = 1, and
// (R[*m-1] ##1 R[*1:$]) for m > 1.
std::shared_ptr<const SequenceExpr> SeqRepeatAtLeast(
    std::shared_ptr<const SequenceExpr> r, unsigned int m);

// R[*], which is (R[*0] or R[*1:$]), and R[+], which is R[*1:$].
std::shared_ptr<const SequenceExpr> SeqRepeatZeroOrMore(
    std::shared_ptr<const SequenceExpr> r);
std::shared_ptr<const SequenceExpr> SeqRepeatOneOrMore(
    std::shared_ptr<const SequenceExpr> r);

}  // namespace delta
