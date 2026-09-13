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

}  // namespace delta
