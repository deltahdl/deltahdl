#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

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

// A spread of operand match sets, each given as the set of clock ticks on which
// a match of the underlying sequence_expr ends. The empty set is the no-match
// case; the others cover a single match, several distinct end ticks, and ties
// on the earliest end tick — the shapes §16.9.8 first_match reduces.
const std::vector<std::vector<uint32_t>> kOperandMatchSets = {
    {}, {7}, {5, 3, 4, 2}, {4, 4, 6}, {3, 3, 3},
};

// §16.12.2: strong(sequence_expr) is equivalent to
// strong(first_match(sequence_expr)) because a nonempty match of the sequence
// exists exactly when one exists for its first_match. Rather than assert this
// by an identity, drive the operand match set through the real §16.9.8
// first_match reduction (EvalFirstMatch) and confirm the strong verdict is
// unchanged: strong holds iff the operand had any match, and first_match
// preserves that existence.
TEST(SequenceProperty, StrongEqualsStrongOfFirstMatch) {
  for (const auto& match_set : kOperandMatchSets) {
    bool seq_has_match = !match_set.empty();
    bool first_match_has_match = EvalFirstMatch(match_set).matched;
    EXPECT_EQ(EvalStrongSequenceProperty(seq_has_match),
              EvalStrongSequenceProperty(first_match_has_match));
  }
}

// §16.12.2: weak(sequence_expr) is equivalent to
// weak(first_match(sequence_expr)) because a finite prefix witnesses inability
// to match the sequence exactly when it does for its first_match. Model the
// witness as the absence of any match over the observed word, and derive the
// first_match side through the real EvalFirstMatch reduction: because
// first_match keeps a match exactly when the operand had one, the two inability
// observations agree and the weak verdict is the same.
TEST(SequenceProperty, WeakEqualsWeakOfFirstMatch) {
  for (const auto& match_set : kOperandMatchSets) {
    bool seq_prefix_inability = match_set.empty();
    bool first_match_prefix_inability = !EvalFirstMatch(match_set).matched;
    EXPECT_EQ(EvalWeakSequenceProperty(seq_prefix_inability),
              EvalWeakSequenceProperty(first_match_prefix_inability));
  }
}

}  // namespace
