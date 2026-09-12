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

// §F.3.4.2.2: the derived delay and concatenation operators of §16.9.1,
// unfolded into ##1, ##0 and a consecutive repetition of the constant 1 that
// stands for the ticks the delay spans. The unary forms put the repetition
// before R; the binary forms put one tick fewer between R1 and R2, since the
// ##1 that joins them is a tick of its own, and a delay that may be zero
// unfolds to an or whose first alternative is the fusion R1 ##0 R2.

// ##[m:n] R for m <= n, which is (1[*m:n] ##1 R); ##[m:$] R, which is
// (1[*m:$] ##1 R); and ##m R, which is (1[*m] ##1 R).
std::shared_ptr<const SequenceExpr> SeqDelayRange(
    unsigned int m, unsigned int n, std::shared_ptr<const SequenceExpr> r);
std::shared_ptr<const SequenceExpr> SeqDelayAtLeast(
    unsigned int m, std::shared_ptr<const SequenceExpr> r);
std::shared_ptr<const SequenceExpr> SeqDelayExactly(
    unsigned int m, std::shared_ptr<const SequenceExpr> r);

// ##[*] R, which is ##[0:$] R, and ##[+] R, which is ##[1:$] R.
std::shared_ptr<const SequenceExpr> SeqDelayZeroOrMore(
    std::shared_ptr<const SequenceExpr> r);
std::shared_ptr<const SequenceExpr> SeqDelayOneOrMore(
    std::shared_ptr<const SequenceExpr> r);

// R1 ##[m:n] R2 for m <= n: (R1 ##1 1[*m-1:n-1] ##1 R2) for m > 0,
// (R1 ##0 R2) for m = n = 0, and ((R1 ##0 R2) or (R1 ##[1:n] R2)) for m = 0
// under a positive n.
std::shared_ptr<const SequenceExpr> SeqConcatDelayRange(
    std::shared_ptr<const SequenceExpr> r1, unsigned int m, unsigned int n,
    std::shared_ptr<const SequenceExpr> r2);

// R1 ##[m:$] R2: (R1 ##1 1[*m-1:$] ##1 R2) for m > 0 and
// ((R1 ##0 R2) or (R1 ##[1:$] R2)) for m = 0.
std::shared_ptr<const SequenceExpr> SeqConcatDelayAtLeast(
    std::shared_ptr<const SequenceExpr> r1, unsigned int m,
    std::shared_ptr<const SequenceExpr> r2);

// R1 ##m R2: (R1 ##1 1[*m-1] ##1 R2) for m > 1, and the primitives
// (R1 ##1 R2) and (R1 ##0 R2) for m = 1 and m = 0, which §F.3.2 has and
// §F.3.4.2.2 therefore leaves as they are.
std::shared_ptr<const SequenceExpr> SeqConcatDelayExactly(
    std::shared_ptr<const SequenceExpr> r1, unsigned int m,
    std::shared_ptr<const SequenceExpr> r2);

// §F.3.4.2.3: the derived nonconsecutive repetition operators of §16.9.2, over
// a Boolean b. A goto repetition b[->m:n] is the consecutive repetition
// (!b[*0:$] ##1 b)[*m:n] of a unit that runs through letters without b and
// ends at one with it, so the word ends at the last b; a nonconsecutive
// repetition b[=m:n] is (b[->m:n] ##1 !b[*0:$]), the same followed by a run
// of letters without b. The bounded, unbounded and exact forms unfold through
// the §F.3.4.2.1 repetitions of the same shape.
std::shared_ptr<const SequenceExpr> SeqGotoRange(
    const std::shared_ptr<const BooleanExpr>& b, unsigned int m,
    unsigned int n);
std::shared_ptr<const SequenceExpr> SeqGotoAtLeast(
    const std::shared_ptr<const BooleanExpr>& b, unsigned int m);
std::shared_ptr<const SequenceExpr> SeqGotoExactly(
    const std::shared_ptr<const BooleanExpr>& b, unsigned int m);
std::shared_ptr<const SequenceExpr> SeqNonconsecutiveRange(
    const std::shared_ptr<const BooleanExpr>& b, unsigned int m,
    unsigned int n);
std::shared_ptr<const SequenceExpr> SeqNonconsecutiveAtLeast(
    const std::shared_ptr<const BooleanExpr>& b, unsigned int m);
std::shared_ptr<const SequenceExpr> SeqNonconsecutiveExactly(
    const std::shared_ptr<const BooleanExpr>& b, unsigned int m);

}  // namespace delta
