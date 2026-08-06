#include <gtest/gtest.h>

#include "simulator/sva_engine.h"

using namespace delta;

namespace {

// §16.12.3: `not property_expr` returns the opposite of the underlying
// property_expr. A true underlying evaluation makes the negation false.
TEST(NegationProperty, NotOfTrueIsFalse) {
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kPass), PropertyResult::kFail);
}

// §16.12.3: a false underlying evaluation makes the negation true.
TEST(NegationProperty, NotOfFalseIsTrue) {
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kFail), PropertyResult::kPass);
}

// §16.12.3: the negation is the complement of the underlying verdict, and each
// attempt of the negation drives exactly one attempt of property_expr — so the
// result is a total function of that single underlying verdict. A vacuous pass
// counts as the property holding, so its negation fails.
TEST(NegationProperty, ComplementOfEveryUnderlyingVerdict) {
  EXPECT_EQ(EvalPropertyNot(EvalPropertyNot(PropertyResult::kPass)),
            PropertyResult::kPass);
  EXPECT_EQ(EvalPropertyNot(EvalPropertyNot(PropertyResult::kFail)),
            PropertyResult::kFail);
  EXPECT_EQ(EvalPropertyNot(PropertyResult::kVacuousPass),
            PropertyResult::kFail);
}

// §16.12.3: the `not` operator switches the strength of the property it
// negates — a weak property becomes strong.
TEST(NegationProperty, NegationMakesWeakStrong) {
  EXPECT_EQ(NegatePropertyStrength(SequencePropertyStrength::kWeak),
            SequencePropertyStrength::kStrong);
}

// §16.12.3: negating a strong property yields a weak one. This is why the LRM
// recommends `not strong(a ##1 b)` over a bare `not a ##1 b` in an assertion:
// the bare sequence is weak, so its negation stays weak.
TEST(NegationProperty, NegationMakesStrongWeak) {
  EXPECT_EQ(NegatePropertyStrength(SequencePropertyStrength::kStrong),
            SequencePropertyStrength::kWeak);
}

}  // namespace
