#include <gtest/gtest.h>

#include "simulator/sva_engine.h"

using namespace delta;

namespace {

// §16.12.2: when the strong/weak operator is omitted, a bare sequence_expr is
// evaluated weakly inside an assert property or assume property statement.
TEST(SequenceProperty, BareSequenceIsWeakUnderAssertAndAssume) {
  EXPECT_EQ(DefaultSequencePropertyStrength(AssertionKind::kAssert),
            SequencePropertyStrength::kWeak);
  EXPECT_EQ(DefaultSequencePropertyStrength(AssertionKind::kAssume),
            SequencePropertyStrength::kWeak);
}

// §16.12.2: a bare sequence_expr is evaluated strongly inside every other
// assertion statement (the "otherwise" case, e.g. cover property).
TEST(SequenceProperty, BareSequenceIsStrongOtherwise) {
  EXPECT_EQ(DefaultSequencePropertyStrength(AssertionKind::kCover),
            SequencePropertyStrength::kStrong);
  EXPECT_EQ(DefaultSequencePropertyStrength(AssertionKind::kRestrict),
            SequencePropertyStrength::kStrong);
}

// §16.12.2: strong(sequence_expr) evaluates to true if, and only if, there is a
// nonempty match of the sequence_expr. Because a single match suffices, this is
// equivalent to strong(first_match(sequence_expr)).
TEST(SequenceProperty, StrongHoldsExactlyWhenNonemptyMatchExists) {
  EXPECT_EQ(EvalStrongSequenceProperty(/*has_nonempty_match=*/true),
            PropertyResult::kPass);
  EXPECT_EQ(EvalStrongSequenceProperty(/*has_nonempty_match=*/false),
            PropertyResult::kFail);
}

// §16.12.2: weak(sequence_expr) evaluates to true if, and only if, no finite
// prefix witnesses inability to match the sequence_expr. Equivalent to
// weak(first_match(sequence_expr)).
TEST(SequenceProperty, WeakFailsOnlyWhenAPrefixWitnessesInability) {
  EXPECT_EQ(
      EvalWeakSequenceProperty(/*finite_prefix_witnesses_inability=*/false),
      PropertyResult::kPass);
  EXPECT_EQ(
      EvalWeakSequenceProperty(/*finite_prefix_witnesses_inability=*/true),
      PropertyResult::kFail);
}

// §16.12.2: strong(sequence_expr) is equivalent to
// strong(first_match(sequence_expr)) because a nonempty match of the sequence
// exists exactly when one exists for its first_match. The strong evaluator
// depends only on that preserved observation, so it returns the same verdict
// whether or not first_match wraps the sequence.
TEST(SequenceProperty, StrongEqualsStrongOfFirstMatch) {
  // first_match preserves whether a nonempty match exists.
  auto nonempty_match_of_first_match = [](bool of_seq) { return of_seq; };
  for (bool has_match : {false, true}) {
    EXPECT_EQ(
        EvalStrongSequenceProperty(has_match),
        EvalStrongSequenceProperty(nonempty_match_of_first_match(has_match)));
  }
}

// §16.12.2: weak(sequence_expr) is equivalent to
// weak(first_match(sequence_expr)) because a finite prefix witnesses inability
// to match the sequence exactly when it does for its first_match. The weak
// evaluator depends only on that preserved observation.
TEST(SequenceProperty, WeakEqualsWeakOfFirstMatch) {
  // A prefix witnesses inability for the sequence iff for its first_match.
  auto prefix_inability_of_first_match = [](bool of_seq) { return of_seq; };
  for (bool witnessed : {false, true}) {
    EXPECT_EQ(
        EvalWeakSequenceProperty(witnessed),
        EvalWeakSequenceProperty(prefix_inability_of_first_match(witnessed)));
  }
}

}  // namespace
