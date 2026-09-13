#pragma once

#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_property_rewrite.h"

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

// §F.3.4.2.4: the other derived sequence operators, unfolded into intersect,
// ##1, ##0 and the repetitions above.

// (R1 and R2), which is (((R1 ##1 1[*0:$]) intersect R2) or (R1 intersect
// (R2 ##1 1[*0:$]))): both operands match from the same letter and the word
// ends where the longer of them does.
std::shared_ptr<const SequenceExpr> SeqAnd(
    std::shared_ptr<const SequenceExpr> r1,
    std::shared_ptr<const SequenceExpr> r2);

// (R1 within R2), which is ((1[*0:$] ##1 R1 ##1 1[*0:$]) intersect R2): R1
// matches somewhere inside a match of R2.
std::shared_ptr<const SequenceExpr> SeqWithin(
    std::shared_ptr<const SequenceExpr> r1,
    std::shared_ptr<const SequenceExpr> r2);

// (b throughout R), which is ((b[*0:$]) intersect R): b holds at every letter
// of a match of R.
std::shared_ptr<const SequenceExpr> SeqThroughout(
    const std::shared_ptr<const BooleanExpr>& b,
    std::shared_ptr<const SequenceExpr> r);

// (R, v1 = e1, ..., vk = ek) for k >= 1: (R ##0 (1, v1 = e1)) for one
// assignment, and ((R, v1 = e1) ##0 (1, v2 = e2, ..., vk = ek)) above, the
// second operand unfolding the same way until one assignment is left. The
// grammar's sampling form records the name alone, as (1, v = e) does in
// §F.3.2, so the assignments are given by their names.
std::shared_ptr<const SequenceExpr> SeqWithLocalAssignments(
    std::shared_ptr<const SequenceExpr> r,
    const std::vector<std::string>& names);

// §F.3.4.3.1: the derived sequential property. A sequence R written where a
// property is expected stands for strong(R) in a cover property or expect
// statement and for weak(R) in an assert property or assume property
// statement, which by §F.3.4.1 is where a restrict property statement stands
// too. The statement is the context, since the same R reads two ways.
enum class SequencePropertyContext : std::uint8_t {
  kAssertProperty,
  kAssumeProperty,
  kCoverProperty,
  kRestrictProperty,
  kExpect,
};

// True where §F.3.4.3.1 reads a bare sequence as strong(R) in the context,
// false where it reads it as weak(R).
bool BareSequenceIsStrong(SequencePropertyContext context);

// The §F.3.2 property a bare sequence stands for in the context, in the
// unclocked property model of §F.5.3.1 and in the clocked one of §F.5.1.2.
std::shared_ptr<const PropertyExpr> PropOfBareSequence(
    std::shared_ptr<const SequenceExpr> r, SequencePropertyContext context);
std::shared_ptr<const ClockedProperty> ClkOfBareSequence(
    std::shared_ptr<const SequenceExpr> r, SequencePropertyContext context);

// §F.3.4.3.2: the derived Boolean property operators, unfolded into the
// §F.3.2 not, or and and. (p1 implies p2) is (not p1 or p2), so it holds
// wherever p1 fails or p2 holds; (p1 iff p2) is ((p1 implies p2) and
// (p2 implies p1)), so it holds where the two agree. Each is given in the
// unclocked property model of §F.5.3.1 and in the clocked one of §F.5.1.2.
std::shared_ptr<const PropertyExpr> PropImplies(
    std::shared_ptr<const PropertyExpr> p1,
    std::shared_ptr<const PropertyExpr> p2);
std::shared_ptr<const PropertyExpr> PropIff(
    std::shared_ptr<const PropertyExpr> p1,
    std::shared_ptr<const PropertyExpr> p2);
std::shared_ptr<const ClockedProperty> ClkImplies(
    std::shared_ptr<const ClockedProperty> p1,
    std::shared_ptr<const ClockedProperty> p2);
std::shared_ptr<const ClockedProperty> ClkIff(
    std::shared_ptr<const ClockedProperty> p1,
    std::shared_ptr<const ClockedProperty> p2);

// §F.3.4.3.3: the derived nonoverlapping implication operator, unfolded into
// the §F.3.2 overlapping implication |-> over an antecedent lengthened by one
// letter, so the consequent is evaluated from the letter after the one the
// antecedent's match ends at. Over an unclocked sequence R and property P,
// (R |=> P) is ((R ##1 1) |-> P), the unclocked property model of §F.5.3.1;
// over a clocked sequence S and property Q, (S |=> Q) is ((S ##1 @(1) 1) |->
// Q), the clocked one of §F.5.1.2, where the clock form on the constant 1
// keeps that letter a letter rather than a tick of whatever clock S is under.
std::shared_ptr<const PropertyExpr> PropNonoverlappingImplication(
    std::shared_ptr<const SequenceExpr> r,
    std::shared_ptr<const PropertyExpr> p);
std::shared_ptr<const ClockedProperty> ClkNonoverlappingImplication(
    std::shared_ptr<const SequenceExpr> s,
    std::shared_ptr<const ClockedProperty> q);

// §F.3.4.3.4: the derived conditional operators, unfolded into the §F.3.2
// overlapping implication over the Boolean b read as a one-letter sequence.
// (if (b) P) is (b |-> P), so P is required where b holds at the first letter
// and nothing is required where it does not. (if (b) P1 else P2) is
// ((b |-> P1) and (weak(b) or P2)): the first conjunct requires P1 where b
// holds, and the second, since weak(b) holds exactly where b does at the
// first letter, requires P2 where b fails. Each is given in the unclocked
// property model of §F.5.3.1 and in the clocked one of §F.5.1.2.
std::shared_ptr<const PropertyExpr> PropIf(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const PropertyExpr> p);
std::shared_ptr<const PropertyExpr> PropIfElse(
    const std::shared_ptr<const BooleanExpr>& b,
    std::shared_ptr<const PropertyExpr> p1,
    std::shared_ptr<const PropertyExpr> p2);
std::shared_ptr<const ClockedProperty> ClkIf(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const ClockedProperty> q);
std::shared_ptr<const ClockedProperty> ClkIfElse(
    const std::shared_ptr<const BooleanExpr>& b,
    std::shared_ptr<const ClockedProperty> q1,
    std::shared_ptr<const ClockedProperty> q2);

// §F.3.4.3.5: the derived case operators, unfolded into the §F.3.4.3.4
// conditional operators over the Boolean specify(b) === specify(b_i) each
// item's match is. The subclause lets specify(b) be the function that expands
// b and treats it as signed or unsigned by the §12.5 rules for comparing the
// expressions of a case statement, and the §F.3.2 Boolean model carries no
// comparison form, so the Boolean that match denotes is supplied by the
// caller as a CaseMatch, which each factory calls on b and the b_i of each
// item in turn. The identities are then: a case with a default alone is that
// default; one item without a default is (if (match) P1); one item with a
// default is (if (match) P1 else Pd); and more items are
// (if (match) P1 else case ...) over the remaining items and the default,
// where the subclause nests the case over specify(b) and the match is the
// same, since expanding and signing an expression a second time changes
// nothing. A case with neither an item nor a default names no property and
// yields null.
using CaseMatch = std::function<std::shared_ptr<const BooleanExpr>(
    const std::shared_ptr<const BooleanExpr>& b,
    const std::shared_ptr<const BooleanExpr>& item)>;

struct PropCaseItem {
  std::shared_ptr<const BooleanExpr> b;
  std::shared_ptr<const PropertyExpr> property;
};
struct ClkCaseItem {
  std::shared_ptr<const BooleanExpr> b;
  std::shared_ptr<const ClockedProperty> property;
};

std::shared_ptr<const PropertyExpr> PropCase(
    const std::shared_ptr<const BooleanExpr>& b,
    const std::vector<PropCaseItem>& items,
    std::shared_ptr<const PropertyExpr> default_property,
    const CaseMatch& match);
std::shared_ptr<const ClockedProperty> ClkCase(
    const std::shared_ptr<const BooleanExpr>& b,
    const std::vector<ClkCaseItem>& items,
    std::shared_ptr<const ClockedProperty> default_property,
    const CaseMatch& match);

// §F.3.4.3.6: the derived followed_by operators, unfolded into the negation
// of an implication over the negated consequent. (r #-# p) is
// (not (r |-> not p)), so where the implication would require p to fail from
// the letter every match of r ends at, the followed_by requires p to hold from
// the letter some match of r ends at; and (r #=# p) is (not (r |=> not p)),
// the same over the §F.3.4.3.3 nonoverlapping implication, so p is required
// from the letter after some match of r. Neither holds where r has no match,
// since the implication then holds vacuously and its negation does not. Each
// is given in the unclocked property model of §F.5.3.1 and in the clocked one
// of §F.5.1.2.
std::shared_ptr<const PropertyExpr> PropFollowedBy(
    std::shared_ptr<const SequenceExpr> r,
    std::shared_ptr<const PropertyExpr> p);
std::shared_ptr<const PropertyExpr> PropNonoverlappingFollowedBy(
    std::shared_ptr<const SequenceExpr> r,
    std::shared_ptr<const PropertyExpr> p);
std::shared_ptr<const ClockedProperty> ClkFollowedBy(
    std::shared_ptr<const SequenceExpr> s,
    std::shared_ptr<const ClockedProperty> q);
std::shared_ptr<const ClockedProperty> ClkNonoverlappingFollowedBy(
    std::shared_ptr<const SequenceExpr> s,
    std::shared_ptr<const ClockedProperty> q);

// §F.3.4.3.7: the derived abort operators, unfolded into the §F.3.2 accept_on
// form and negation. (reject_on(b) P) is (not accept_on(b) not P): where the
// accept_on holds once P holds on the word or on the completion of some
// prefix cut at a letter satisfying b, the reject_on holds only where P holds
// on the word and on every such completion. (sync_accept_on(b) P) is
// (accept_on(b) P) when the clock context is 1, which is the context the
// unclocked model of §F.5.3.1 evaluates in, so PropSyncAcceptOn is the
// accept_on itself there; under a clock, the §F.5.1.2 ClkSyncAcceptOn form
// keeps the abort sampled with the clock and stands in its own right. And
// (sync_reject_on(b) P) is (not (sync_accept_on(b) not P)), the same
// negation over the synchronous form. Each is given in the unclocked property
// model of §F.5.3.1 and in the clocked one of §F.5.1.2.
std::shared_ptr<const PropertyExpr> PropRejectOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const PropertyExpr> p);
std::shared_ptr<const PropertyExpr> PropSyncAcceptOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const PropertyExpr> p);
std::shared_ptr<const PropertyExpr> PropSyncRejectOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const PropertyExpr> p);
std::shared_ptr<const ClockedProperty> ClkRejectOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const ClockedProperty> q);
std::shared_ptr<const ClockedProperty> ClkSyncRejectOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const ClockedProperty> q);

// §F.3.4.3.8: the derived unbounded temporal operators, unfolded into the
// §F.3.2 until, not and and. (always p) is (p until 0): the release
// condition is the Boolean 0, which no letter satisfies, so the until never
// releases and p is required from every letter. (s_eventually p) is
// (not (always (not p))), so p is required from some letter.
// (p s_until q) is ((p until q) and s_eventually q): the until, which also
// holds where q never releases it, strengthened by the requirement that q hold
// from some letter. (p until_with q) is (p until (p and q)), so p holds from
// the letter that releases the until as well as from those before it; and
// (p s_until_with q) is (p s_until (p and q)), the same over the strong
// until. Each is given in the unclocked property model of §F.5.3.1, where the
// Boolean 0 in property position is read as strong(0) by the convention the
// §F.5.3.1 layer applies to a Boolean T^p emits, and in the clocked one of
// §F.5.1.2, where it is the Boolean property 0 that T^p leaves as it is.
std::shared_ptr<const PropertyExpr> PropAlways(
    std::shared_ptr<const PropertyExpr> p);
std::shared_ptr<const PropertyExpr> PropSEventually(
    std::shared_ptr<const PropertyExpr> p);
std::shared_ptr<const PropertyExpr> PropSUntil(
    const std::shared_ptr<const PropertyExpr>& p,
    const std::shared_ptr<const PropertyExpr>& q);
std::shared_ptr<const PropertyExpr> PropUntilWith(
    const std::shared_ptr<const PropertyExpr>& p,
    std::shared_ptr<const PropertyExpr> q);
std::shared_ptr<const PropertyExpr> PropSUntilWith(
    const std::shared_ptr<const PropertyExpr>& p,
    std::shared_ptr<const PropertyExpr> q);
std::shared_ptr<const ClockedProperty> ClkAlways(
    std::shared_ptr<const ClockedProperty> q);
std::shared_ptr<const ClockedProperty> ClkSEventually(
    std::shared_ptr<const ClockedProperty> q);
std::shared_ptr<const ClockedProperty> ClkSUntil(
    const std::shared_ptr<const ClockedProperty>& q1,
    const std::shared_ptr<const ClockedProperty>& q2);
std::shared_ptr<const ClockedProperty> ClkUntilWith(
    const std::shared_ptr<const ClockedProperty>& q1,
    std::shared_ptr<const ClockedProperty> q2);
std::shared_ptr<const ClockedProperty> ClkSUntilWith(
    const std::shared_ptr<const ClockedProperty>& q1,
    std::shared_ptr<const ClockedProperty> q2);

}  // namespace delta
