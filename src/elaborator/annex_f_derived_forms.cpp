#include "elaborator/annex_f_derived_forms.h"

#include <memory>
#include <utility>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_neutral_satisfaction.h"

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

}  // namespace delta
