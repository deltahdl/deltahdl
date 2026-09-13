#include "elaborator/annex_f_derived_forms.h"

#include <memory>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"
#include "elaborator/annex_f_property_rewrite.h"

namespace delta {

AssertionStatement::Role RoleOfConcurrentAssertionDirective(
    ConcurrentAssertionDirective directive) {
  switch (directive) {
    case ConcurrentAssertionDirective::kAssert:
      return AssertionStatement::Role::kAssert;
    case ConcurrentAssertionDirective::kCover:
      return AssertionStatement::Role::kCover;
    case ConcurrentAssertionDirective::kAssume:
    case ConcurrentAssertionDirective::kRestrict:
      return AssertionStatement::Role::kAssume;
  }
  return AssertionStatement::Role::kAssume;
}

std::shared_ptr<const SequenceExpr> SeqRepeatExactly(
    std::shared_ptr<const SequenceExpr> r, unsigned int m) {
  if (m == 0) return SeqNullRepeat(std::move(r));
  auto fewer = SeqRepeatExactly(r, m - 1);
  return SeqConcat(std::move(fewer), std::move(r));
}

std::shared_ptr<const SequenceExpr> SeqRepeatRange(
    std::shared_ptr<const SequenceExpr> r, unsigned int m, unsigned int n) {
  if (m == n) return SeqRepeatExactly(std::move(r), m);
  auto narrower = SeqRepeatRange(r, m, n - 1);
  return SeqOr(std::move(narrower), SeqRepeatExactly(std::move(r), n));
}

std::shared_ptr<const SequenceExpr> SeqRepeatAtLeast(
    std::shared_ptr<const SequenceExpr> r, unsigned int m) {
  if (m == 0) return SeqRepeatZeroOrMore(std::move(r));
  if (m == 1) return SeqUnboundedRepeat(std::move(r));
  auto fewer = SeqRepeatExactly(r, m - 1);
  return SeqConcat(std::move(fewer), SeqUnboundedRepeat(std::move(r)));
}

std::shared_ptr<const SequenceExpr> SeqRepeatZeroOrMore(
    std::shared_ptr<const SequenceExpr> r) {
  return SeqOr(SeqNullRepeat(r), SeqUnboundedRepeat(std::move(r)));
}

std::shared_ptr<const SequenceExpr> SeqRepeatOneOrMore(
    std::shared_ptr<const SequenceExpr> r) {
  return SeqUnboundedRepeat(std::move(r));
}

// The constant 1 as a sequence, the operand every delay's repetition spans.
static std::shared_ptr<const SequenceExpr> SeqTrue() {
  return SeqBoolean(BoolTrue());
}

std::shared_ptr<const SequenceExpr> SeqDelayRange(
    unsigned int m, unsigned int n, std::shared_ptr<const SequenceExpr> r) {
  return SeqConcat(SeqRepeatRange(SeqTrue(), m, n), std::move(r));
}

std::shared_ptr<const SequenceExpr> SeqDelayAtLeast(
    unsigned int m, std::shared_ptr<const SequenceExpr> r) {
  return SeqConcat(SeqRepeatAtLeast(SeqTrue(), m), std::move(r));
}

std::shared_ptr<const SequenceExpr> SeqDelayExactly(
    unsigned int m, std::shared_ptr<const SequenceExpr> r) {
  return SeqConcat(SeqRepeatExactly(SeqTrue(), m), std::move(r));
}

std::shared_ptr<const SequenceExpr> SeqDelayZeroOrMore(
    std::shared_ptr<const SequenceExpr> r) {
  return SeqDelayAtLeast(0, std::move(r));
}

std::shared_ptr<const SequenceExpr> SeqDelayOneOrMore(
    std::shared_ptr<const SequenceExpr> r) {
  return SeqDelayAtLeast(1, std::move(r));
}

// (R1 ##1 gap ##1 R2), grouped to the left as §F.3.4's convention allows.
static std::shared_ptr<const SequenceExpr> SeqConcatAcrossGap(
    std::shared_ptr<const SequenceExpr> r1,
    std::shared_ptr<const SequenceExpr> gap,
    std::shared_ptr<const SequenceExpr> r2) {
  return SeqConcat(SeqConcat(std::move(r1), std::move(gap)), std::move(r2));
}

std::shared_ptr<const SequenceExpr> SeqConcatDelayRange(
    std::shared_ptr<const SequenceExpr> r1, unsigned int m, unsigned int n,
    std::shared_ptr<const SequenceExpr> r2) {
  if (m > 0) {
    return SeqConcatAcrossGap(
        std::move(r1), SeqRepeatRange(SeqTrue(), m - 1, n - 1), std::move(r2));
  }
  if (n == 0) return SeqFusion(std::move(r1), std::move(r2));
  auto fused = SeqFusion(r1, r2);
  return SeqOr(std::move(fused),
               SeqConcatDelayRange(std::move(r1), 1, n, std::move(r2)));
}

std::shared_ptr<const SequenceExpr> SeqConcatDelayAtLeast(
    std::shared_ptr<const SequenceExpr> r1, unsigned int m,
    std::shared_ptr<const SequenceExpr> r2) {
  if (m > 0) {
    return SeqConcatAcrossGap(std::move(r1), SeqRepeatAtLeast(SeqTrue(), m - 1),
                              std::move(r2));
  }
  auto fused = SeqFusion(r1, r2);
  return SeqOr(std::move(fused),
               SeqConcatDelayAtLeast(std::move(r1), 1, std::move(r2)));
}

std::shared_ptr<const SequenceExpr> SeqConcatDelayExactly(
    std::shared_ptr<const SequenceExpr> r1, unsigned int m,
    std::shared_ptr<const SequenceExpr> r2) {
  if (m > 1) {
    return SeqConcatAcrossGap(std::move(r1), SeqRepeatExactly(SeqTrue(), m - 1),
                              std::move(r2));
  }
  if (m == 1) return SeqConcat(std::move(r1), std::move(r2));
  return SeqFusion(std::move(r1), std::move(r2));
}

// !b[*0:$], the run of letters without b that a goto repetition's unit opens
// with and a nonconsecutive repetition ends with, in the §F.3.4.2.1 unfolding
// of [*0:$].
static std::shared_ptr<const SequenceExpr> SeqRunWithout(
    const std::shared_ptr<const BooleanExpr>& b) {
  return SeqRepeatAtLeast(SeqBoolean(BoolNot(b)), 0);
}

// (!b[*0:$] ##1 b), the unit a goto repetition repeats.
static std::shared_ptr<const SequenceExpr> SeqGotoUnit(
    const std::shared_ptr<const BooleanExpr>& b) {
  return SeqConcat(SeqRunWithout(b), SeqBoolean(b));
}

std::shared_ptr<const SequenceExpr> SeqGotoRange(
    const std::shared_ptr<const BooleanExpr>& b, unsigned int m,
    unsigned int n) {
  return SeqRepeatRange(SeqGotoUnit(b), m, n);
}

std::shared_ptr<const SequenceExpr> SeqGotoAtLeast(
    const std::shared_ptr<const BooleanExpr>& b, unsigned int m) {
  return SeqRepeatAtLeast(SeqGotoUnit(b), m);
}

std::shared_ptr<const SequenceExpr> SeqGotoExactly(
    const std::shared_ptr<const BooleanExpr>& b, unsigned int m) {
  return SeqRepeatExactly(SeqGotoUnit(b), m);
}

std::shared_ptr<const SequenceExpr> SeqNonconsecutiveRange(
    const std::shared_ptr<const BooleanExpr>& b, unsigned int m,
    unsigned int n) {
  auto gotos = SeqGotoRange(b, m, n);
  return SeqConcat(std::move(gotos), SeqRunWithout(b));
}

std::shared_ptr<const SequenceExpr> SeqNonconsecutiveAtLeast(
    const std::shared_ptr<const BooleanExpr>& b, unsigned int m) {
  auto gotos = SeqGotoAtLeast(b, m);
  return SeqConcat(std::move(gotos), SeqRunWithout(b));
}

std::shared_ptr<const SequenceExpr> SeqNonconsecutiveExactly(
    const std::shared_ptr<const BooleanExpr>& b, unsigned int m) {
  auto gotos = SeqGotoExactly(b, m);
  return SeqConcat(std::move(gotos), SeqRunWithout(b));
}

// 1[*0:$], the padding that lets one operand of and or within run on past the
// other, in the §F.3.4.2.1 unfolding of [*0:$].
static std::shared_ptr<const SequenceExpr> SeqAnyRun() {
  return SeqRepeatAtLeast(SeqTrue(), 0);
}

std::shared_ptr<const SequenceExpr> SeqAnd(
    std::shared_ptr<const SequenceExpr> r1,
    std::shared_ptr<const SequenceExpr> r2) {
  auto first_padded = SeqIntersect(SeqConcat(r1, SeqAnyRun()), r2);
  auto second_padded =
      SeqIntersect(std::move(r1), SeqConcat(std::move(r2), SeqAnyRun()));
  return SeqOr(std::move(first_padded), std::move(second_padded));
}

std::shared_ptr<const SequenceExpr> SeqWithin(
    std::shared_ptr<const SequenceExpr> r1,
    std::shared_ptr<const SequenceExpr> r2) {
  auto padded = SeqConcat(SeqConcat(SeqAnyRun(), std::move(r1)), SeqAnyRun());
  return SeqIntersect(std::move(padded), std::move(r2));
}

std::shared_ptr<const SequenceExpr> SeqThroughout(
    const std::shared_ptr<const BooleanExpr>& b,
    std::shared_ptr<const SequenceExpr> r) {
  return SeqIntersect(SeqRepeatAtLeast(SeqBoolean(b), 0), std::move(r));
}

std::shared_ptr<const SequenceExpr> SeqWithLocalAssignments(
    std::shared_ptr<const SequenceExpr> r,
    const std::vector<std::string>& names) {
  auto first = SeqFusion(std::move(r), SeqLocalVarSampling(names.front()));
  if (names.size() == 1) return first;
  std::vector<std::string> rest(names.begin() + 1, names.end());
  return SeqFusion(std::move(first), SeqWithLocalAssignments(SeqTrue(), rest));
}

bool BareSequenceIsStrong(SequencePropertyContext context) {
  return context == SequencePropertyContext::kCoverProperty ||
         context == SequencePropertyContext::kExpect;
}

std::shared_ptr<const PropertyExpr> PropOfBareSequence(
    std::shared_ptr<const SequenceExpr> r, SequencePropertyContext context) {
  if (BareSequenceIsStrong(context)) return PropStrong(std::move(r));
  return PropWeak(std::move(r));
}

std::shared_ptr<const ClockedProperty> ClkOfBareSequence(
    std::shared_ptr<const SequenceExpr> r, SequencePropertyContext context) {
  if (BareSequenceIsStrong(context)) return ClkStrong(std::move(r));
  return ClkWeak(std::move(r));
}

std::shared_ptr<const PropertyExpr> PropImplies(
    std::shared_ptr<const PropertyExpr> p1,
    std::shared_ptr<const PropertyExpr> p2) {
  return PropOr(PropNot(std::move(p1)), std::move(p2));
}

std::shared_ptr<const PropertyExpr> PropIff(
    std::shared_ptr<const PropertyExpr> p1,
    std::shared_ptr<const PropertyExpr> p2) {
  auto forward = PropImplies(p1, p2);
  return PropAnd(std::move(forward), PropImplies(std::move(p2), std::move(p1)));
}

std::shared_ptr<const ClockedProperty> ClkImplies(
    std::shared_ptr<const ClockedProperty> p1,
    std::shared_ptr<const ClockedProperty> p2) {
  return ClkOr(ClkNot(std::move(p1)), std::move(p2));
}

std::shared_ptr<const ClockedProperty> ClkIff(
    std::shared_ptr<const ClockedProperty> p1,
    std::shared_ptr<const ClockedProperty> p2) {
  auto forward = ClkImplies(p1, p2);
  return ClkAnd(std::move(forward), ClkImplies(std::move(p2), std::move(p1)));
}

std::shared_ptr<const PropertyExpr> PropNonoverlappingImplication(
    std::shared_ptr<const SequenceExpr> r,
    std::shared_ptr<const PropertyExpr> p) {
  return PropImplication(SeqConcat(std::move(r), SeqTrue()), std::move(p));
}

std::shared_ptr<const ClockedProperty> ClkNonoverlappingImplication(
    std::shared_ptr<const SequenceExpr> s,
    std::shared_ptr<const ClockedProperty> q) {
  auto one_letter = SeqClock(BoolTrue(), SeqTrue());
  return ClkImplication(SeqConcat(std::move(s), std::move(one_letter)),
                        std::move(q));
}

std::shared_ptr<const PropertyExpr> PropIf(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const PropertyExpr> p) {
  return PropImplication(SeqBoolean(std::move(b)), std::move(p));
}

std::shared_ptr<const PropertyExpr> PropIfElse(
    const std::shared_ptr<const BooleanExpr>& b,
    std::shared_ptr<const PropertyExpr> p1,
    std::shared_ptr<const PropertyExpr> p2) {
  auto then_branch = PropImplication(SeqBoolean(b), std::move(p1));
  auto else_branch = PropOr(PropWeak(SeqBoolean(b)), std::move(p2));
  return PropAnd(std::move(then_branch), std::move(else_branch));
}

std::shared_ptr<const ClockedProperty> ClkIf(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const ClockedProperty> q) {
  return ClkImplication(SeqBoolean(std::move(b)), std::move(q));
}

std::shared_ptr<const ClockedProperty> ClkIfElse(
    const std::shared_ptr<const BooleanExpr>& b,
    std::shared_ptr<const ClockedProperty> q1,
    std::shared_ptr<const ClockedProperty> q2) {
  auto then_branch = ClkImplication(SeqBoolean(b), std::move(q1));
  auto else_branch = ClkOr(ClkWeak(SeqBoolean(b)), std::move(q2));
  return ClkAnd(std::move(then_branch), std::move(else_branch));
}

namespace {

// The recursion of §F.3.4.3.5 over the items from `first` on: the case over
// no items is the default, and the case over an item followed by others is
// the §F.3.4.3.4 conditional over that item's match, with the case over the
// others as its else where there is one. The same b is nested rather than
// specify(b), which the match already applies.
std::shared_ptr<const PropertyExpr> PropCaseFrom(
    const std::shared_ptr<const BooleanExpr>& b,
    std::vector<PropCaseItem>::const_iterator first,
    std::vector<PropCaseItem>::const_iterator last,
    std::shared_ptr<const PropertyExpr> default_property,
    const CaseMatch& match) {
  if (first == last) {
    return default_property;
  }
  auto condition = match(b, first->b);
  auto rest =
      PropCaseFrom(b, first + 1, last, std::move(default_property), match);
  if (rest == nullptr) {
    return PropIf(std::move(condition), first->property);
  }
  return PropIfElse(condition, first->property, std::move(rest));
}

std::shared_ptr<const ClockedProperty> ClkCaseFrom(
    const std::shared_ptr<const BooleanExpr>& b,
    std::vector<ClkCaseItem>::const_iterator first,
    std::vector<ClkCaseItem>::const_iterator last,
    std::shared_ptr<const ClockedProperty> default_property,
    const CaseMatch& match) {
  if (first == last) {
    return default_property;
  }
  auto condition = match(b, first->b);
  auto rest =
      ClkCaseFrom(b, first + 1, last, std::move(default_property), match);
  if (rest == nullptr) {
    return ClkIf(std::move(condition), first->property);
  }
  return ClkIfElse(condition, first->property, std::move(rest));
}

}  // namespace

std::shared_ptr<const PropertyExpr> PropCase(
    const std::shared_ptr<const BooleanExpr>& b,
    const std::vector<PropCaseItem>& items,
    std::shared_ptr<const PropertyExpr> default_property,
    const CaseMatch& match) {
  return PropCaseFrom(b, items.begin(), items.end(),
                      std::move(default_property), match);
}

std::shared_ptr<const ClockedProperty> ClkCase(
    const std::shared_ptr<const BooleanExpr>& b,
    const std::vector<ClkCaseItem>& items,
    std::shared_ptr<const ClockedProperty> default_property,
    const CaseMatch& match) {
  return ClkCaseFrom(b, items.begin(), items.end(), std::move(default_property),
                     match);
}

std::shared_ptr<const PropertyExpr> PropFollowedBy(
    std::shared_ptr<const SequenceExpr> r,
    std::shared_ptr<const PropertyExpr> p) {
  return PropNot(PropImplication(std::move(r), PropNot(std::move(p))));
}

std::shared_ptr<const PropertyExpr> PropNonoverlappingFollowedBy(
    std::shared_ptr<const SequenceExpr> r,
    std::shared_ptr<const PropertyExpr> p) {
  return PropNot(
      PropNonoverlappingImplication(std::move(r), PropNot(std::move(p))));
}

std::shared_ptr<const ClockedProperty> ClkFollowedBy(
    std::shared_ptr<const SequenceExpr> s,
    std::shared_ptr<const ClockedProperty> q) {
  return ClkNot(ClkImplication(std::move(s), ClkNot(std::move(q))));
}

std::shared_ptr<const ClockedProperty> ClkNonoverlappingFollowedBy(
    std::shared_ptr<const SequenceExpr> s,
    std::shared_ptr<const ClockedProperty> q) {
  return ClkNot(
      ClkNonoverlappingImplication(std::move(s), ClkNot(std::move(q))));
}

std::shared_ptr<const PropertyExpr> PropRejectOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const PropertyExpr> p) {
  return PropNot(PropAcceptOn(std::move(b), PropNot(std::move(p))));
}

std::shared_ptr<const PropertyExpr> PropSyncAcceptOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const PropertyExpr> p) {
  return PropAcceptOn(std::move(b), std::move(p));
}

std::shared_ptr<const PropertyExpr> PropSyncRejectOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const PropertyExpr> p) {
  return PropNot(PropSyncAcceptOn(std::move(b), PropNot(std::move(p))));
}

std::shared_ptr<const ClockedProperty> ClkRejectOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const ClockedProperty> q) {
  return ClkNot(ClkAcceptOn(std::move(b), ClkNot(std::move(q))));
}

std::shared_ptr<const ClockedProperty> ClkSyncRejectOn(
    std::shared_ptr<const BooleanExpr> b,
    std::shared_ptr<const ClockedProperty> q) {
  return ClkNot(ClkSyncAcceptOn(std::move(b), ClkNot(std::move(q))));
}

namespace {

// The Boolean 0 of §F.3.4.3.8, which no letter satisfies, as the §F.3.2
// Boolean !1.
std::shared_ptr<const BooleanExpr> BoolFalse() { return BoolNot(BoolTrue()); }

}  // namespace

std::shared_ptr<const PropertyExpr> PropAlways(
    std::shared_ptr<const PropertyExpr> p) {
  return PropUntil(std::move(p), PropStrong(SeqBoolean(BoolFalse())));
}

std::shared_ptr<const PropertyExpr> PropSEventually(
    std::shared_ptr<const PropertyExpr> p) {
  return PropNot(PropAlways(PropNot(std::move(p))));
}

std::shared_ptr<const PropertyExpr> PropSUntil(
    const std::shared_ptr<const PropertyExpr>& p,
    const std::shared_ptr<const PropertyExpr>& q) {
  return PropAnd(PropUntil(p, q), PropSEventually(q));
}

std::shared_ptr<const PropertyExpr> PropUntilWith(
    const std::shared_ptr<const PropertyExpr>& p,
    std::shared_ptr<const PropertyExpr> q) {
  return PropUntil(p, PropAnd(p, std::move(q)));
}

std::shared_ptr<const PropertyExpr> PropSUntilWith(
    const std::shared_ptr<const PropertyExpr>& p,
    std::shared_ptr<const PropertyExpr> q) {
  return PropSUntil(p, PropAnd(p, std::move(q)));
}

std::shared_ptr<const ClockedProperty> ClkAlways(
    std::shared_ptr<const ClockedProperty> q) {
  return ClkUntil(std::move(q), ClkBoolean(BoolFalse()));
}

std::shared_ptr<const ClockedProperty> ClkSEventually(
    std::shared_ptr<const ClockedProperty> q) {
  return ClkNot(ClkAlways(ClkNot(std::move(q))));
}

std::shared_ptr<const ClockedProperty> ClkSUntil(
    const std::shared_ptr<const ClockedProperty>& q1,
    const std::shared_ptr<const ClockedProperty>& q2) {
  return ClkAnd(ClkUntil(q1, q2), ClkSEventually(q2));
}

std::shared_ptr<const ClockedProperty> ClkUntilWith(
    const std::shared_ptr<const ClockedProperty>& q1,
    std::shared_ptr<const ClockedProperty> q2) {
  return ClkUntil(q1, ClkAnd(q1, std::move(q2)));
}

std::shared_ptr<const ClockedProperty> ClkSUntilWith(
    const std::shared_ptr<const ClockedProperty>& q1,
    std::shared_ptr<const ClockedProperty> q2) {
  return ClkSUntil(q1, ClkAnd(q1, std::move(q2)));
}

std::shared_ptr<const PropertyExpr> PropSNexttime(
    std::shared_ptr<const PropertyExpr> p) {
  return PropNot(PropNexttime(PropNot(std::move(p))));
}

std::shared_ptr<const PropertyExpr> PropNexttimeExactly(
    std::shared_ptr<const PropertyExpr> p, unsigned int m) {
  if (m == 0) return PropImplication(SeqTrue(), std::move(p));
  return PropNexttime(PropNexttimeExactly(std::move(p), m - 1));
}

std::shared_ptr<const PropertyExpr> PropSNexttimeExactly(
    std::shared_ptr<const PropertyExpr> p, unsigned int m) {
  return PropNot(PropNexttimeExactly(PropNot(std::move(p)), m));
}

std::shared_ptr<const PropertyExpr> PropEventuallyRange(
    const std::shared_ptr<const PropertyExpr>& p, unsigned int m,
    unsigned int n) {
  if (m == n) return PropNexttimeExactly(p, m);
  auto narrower = PropEventuallyRange(p, m, n - 1);
  return PropOr(std::move(narrower), PropNexttimeExactly(p, n));
}

std::shared_ptr<const PropertyExpr> PropAlwaysRange(
    const std::shared_ptr<const PropertyExpr>& p, unsigned int m,
    unsigned int n) {
  if (m == n) return PropNexttimeExactly(p, m);
  auto narrower = PropAlwaysRange(p, m, n - 1);
  return PropAnd(std::move(narrower), PropNexttimeExactly(p, n));
}

std::shared_ptr<const PropertyExpr> PropAlwaysAtLeast(
    std::shared_ptr<const PropertyExpr> p, unsigned int m) {
  return PropNexttimeExactly(PropAlways(std::move(p)), m);
}

std::shared_ptr<const PropertyExpr> PropSEventuallyRange(
    std::shared_ptr<const PropertyExpr> p, unsigned int m, unsigned int n) {
  return PropNot(PropAlwaysRange(PropNot(std::move(p)), m, n));
}

std::shared_ptr<const PropertyExpr> PropSEventuallyAtLeast(
    std::shared_ptr<const PropertyExpr> p, unsigned int m) {
  return PropSNexttimeExactly(PropSEventually(std::move(p)), m);
}

std::shared_ptr<const PropertyExpr> PropSAlwaysRange(
    std::shared_ptr<const PropertyExpr> p, unsigned int m, unsigned int n) {
  return PropNot(PropEventuallyRange(PropNot(std::move(p)), m, n));
}

std::shared_ptr<const ClockedProperty> ClkSNexttime(
    std::shared_ptr<const ClockedProperty> q) {
  return ClkNot(ClkNexttime(ClkNot(std::move(q))));
}

std::shared_ptr<const ClockedProperty> ClkNexttimeExactly(
    std::shared_ptr<const ClockedProperty> q, unsigned int m) {
  if (m == 0) return ClkImplication(SeqTrue(), std::move(q));
  return ClkNexttime(ClkNexttimeExactly(std::move(q), m - 1));
}

std::shared_ptr<const ClockedProperty> ClkSNexttimeExactly(
    std::shared_ptr<const ClockedProperty> q, unsigned int m) {
  return ClkNot(ClkNexttimeExactly(ClkNot(std::move(q)), m));
}

std::shared_ptr<const ClockedProperty> ClkEventuallyRange(
    const std::shared_ptr<const ClockedProperty>& q, unsigned int m,
    unsigned int n) {
  if (m == n) return ClkNexttimeExactly(q, m);
  auto narrower = ClkEventuallyRange(q, m, n - 1);
  return ClkOr(std::move(narrower), ClkNexttimeExactly(q, n));
}

std::shared_ptr<const ClockedProperty> ClkAlwaysRange(
    const std::shared_ptr<const ClockedProperty>& q, unsigned int m,
    unsigned int n) {
  if (m == n) return ClkNexttimeExactly(q, m);
  auto narrower = ClkAlwaysRange(q, m, n - 1);
  return ClkAnd(std::move(narrower), ClkNexttimeExactly(q, n));
}

std::shared_ptr<const ClockedProperty> ClkAlwaysAtLeast(
    std::shared_ptr<const ClockedProperty> q, unsigned int m) {
  return ClkNexttimeExactly(ClkAlways(std::move(q)), m);
}

std::shared_ptr<const ClockedProperty> ClkSEventuallyRange(
    std::shared_ptr<const ClockedProperty> q, unsigned int m, unsigned int n) {
  return ClkNot(ClkAlwaysRange(ClkNot(std::move(q)), m, n));
}

std::shared_ptr<const ClockedProperty> ClkSEventuallyAtLeast(
    std::shared_ptr<const ClockedProperty> q, unsigned int m) {
  return ClkSNexttimeExactly(ClkSEventually(std::move(q)), m);
}

std::shared_ptr<const ClockedProperty> ClkSAlwaysRange(
    std::shared_ptr<const ClockedProperty> q, unsigned int m, unsigned int n) {
  return ClkNot(ClkEventuallyRange(ClkNot(std::move(q)), m, n));
}

}  // namespace delta
