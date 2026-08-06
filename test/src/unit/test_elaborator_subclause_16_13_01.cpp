#include <gtest/gtest.h>

#include "elaborator/multiclock_sequence.h"

using namespace delta;

namespace {

// §16.13.1: a singly clocked sequence is a degenerate multiclocked sequence and
// is always legal, even when its subsequence admits the empty match.
TEST(MulticlockSequenceLegality, SinglyClockedSequenceIsLegal) {
  const std::vector<MulticlockSubsequence> kSubsequences = {
      {/*clock=*/"clk", MulticlockJoin::kLeading, /*admits_empty=*/true},
  };
  EXPECT_FALSE(CheckMulticlockSequenceLegality(kSubsequences).has_value());
}

// R1 (§16.13.1): when subsequences governed by different clocks are
// concatenated, every maximal singly clocked subsequence must match only
// nonempty words. Two non-empty-matching subsequences joined by `##1` across a
// clock boundary are legal.
TEST(MulticlockSequenceLegality, DifferentlyClockedNonemptyJoinIsLegal) {
  const std::vector<MulticlockSubsequence> kSubsequences = {
      {/*clock=*/"clk1", MulticlockJoin::kLeading, /*admits_empty=*/false},
      {/*clock=*/"clk2", MulticlockJoin::kSingleDelay, /*admits_empty=*/false},
  };
  EXPECT_FALSE(CheckMulticlockSequenceLegality(kSubsequences).has_value());
}

// R1 (§16.13.1): a maximal singly clocked subsequence that admits the empty
// match makes the clocking event of the join ambiguous, so the multiclocked
// concatenation is illegal. Mirrors `... ##1 @(posedge clk2) sig1[*0:1]`.
TEST(MulticlockSequenceLegality, EmptyMatchingTrailingSubsequenceIsIllegal) {
  const std::vector<MulticlockSubsequence> kSubsequences = {
      {/*clock=*/"clk1", MulticlockJoin::kLeading, /*admits_empty=*/false},
      {/*clock=*/"clk2", MulticlockJoin::kSingleDelay, /*admits_empty=*/true},
  };
  const std::optional<std::string> kError =
      CheckMulticlockSequenceLegality(kSubsequences);
  ASSERT_TRUE(kError.has_value());
  if (!kError.has_value()) return;
  const std::string& error = *kError;
  EXPECT_FALSE(error.empty());
}

// R1 (§16.13.1): the empty-match restriction also rejects an empty-matching
// leading subsequence of a cross-clock concatenation.
TEST(MulticlockSequenceLegality, EmptyMatchingLeadingSubsequenceIsIllegal) {
  const std::vector<MulticlockSubsequence> kSubsequences = {
      {/*clock=*/"clk1", MulticlockJoin::kLeading, /*admits_empty=*/true},
      {/*clock=*/"clk2", MulticlockJoin::kSingleDelay, /*admits_empty=*/false},
  };
  EXPECT_TRUE(CheckMulticlockSequenceLegality(kSubsequences).has_value());
}

// R2 (§16.13.1): the zero-delay concatenation (`##0`) is one of the two
// operators permitted across a clock boundary.
TEST(MulticlockSequenceLegality, DifferentlyClockedZeroDelayJoinIsLegal) {
  const std::vector<MulticlockSubsequence> kSubsequences = {
      {/*clock=*/"clk1", MulticlockJoin::kLeading, /*admits_empty=*/false},
      {/*clock=*/"clk2", MulticlockJoin::kZeroDelay, /*admits_empty=*/false},
  };
  EXPECT_FALSE(CheckMulticlockSequenceLegality(kSubsequences).has_value());
}

// R2 (§16.13.1): an operator other than `##1`/`##0` joining differently clocked
// operands is illegal. Mirrors `s1 ##2 @(posedge clk2) s2` and
// `s1 intersect @(posedge clk2) s2` for non-identical clocks.
TEST(MulticlockSequenceLegality, DifferentlyClockedOtherJoinIsIllegal) {
  const std::vector<MulticlockSubsequence> kSubsequences = {
      {/*clock=*/"clk1", MulticlockJoin::kLeading, /*admits_empty=*/false},
      {/*clock=*/"clk2", MulticlockJoin::kOther, /*admits_empty=*/false},
  };
  const std::optional<std::string> kError =
      CheckMulticlockSequenceLegality(kSubsequences);
  ASSERT_TRUE(kError.has_value());
  if (!kError.has_value()) return;
  const std::string& error = *kError;
  EXPECT_FALSE(error.empty());
}

// R2 (§16.13.1): when the joined operands share a clock the context is singly
// clocked, so operators beyond `##1`/`##0` are not restricted by the
// cross-clock rule.
TEST(MulticlockSequenceLegality, IdenticallyClockedOtherJoinIsLegal) {
  const std::vector<MulticlockSubsequence> kSubsequences = {
      {/*clock=*/"clk", MulticlockJoin::kLeading, /*admits_empty=*/false},
      {/*clock=*/"clk", MulticlockJoin::kOther, /*admits_empty=*/false},
  };
  EXPECT_FALSE(CheckMulticlockSequenceLegality(kSubsequences).has_value());
}

// R1 + R2 (§16.13.1): a chain crossing more than one clock boundary is legal as
// long as every subsequence matches only nonempty words and each boundary is
// joined by `##1` or `##0`. Exercises the legality scan past the first join.
TEST(MulticlockSequenceLegality, MultipleClockBoundariesNonemptyJoinIsLegal) {
  const std::vector<MulticlockSubsequence> kSubsequences = {
      {/*clock=*/"clk1", MulticlockJoin::kLeading, /*admits_empty=*/false},
      {/*clock=*/"clk2", MulticlockJoin::kSingleDelay, /*admits_empty=*/false},
      {/*clock=*/"clk3", MulticlockJoin::kZeroDelay, /*admits_empty=*/false},
  };
  EXPECT_FALSE(CheckMulticlockSequenceLegality(kSubsequences).has_value());
}

// R1 (§16.13.1): the empty-match restriction reaches subsequences in the
// interior of a longer chain, not just the leading or trailing one.
TEST(MulticlockSequenceLegality, EmptyMatchingInteriorSubsequenceIsIllegal) {
  const std::vector<MulticlockSubsequence> kSubsequences = {
      {/*clock=*/"clk1", MulticlockJoin::kLeading, /*admits_empty=*/false},
      {/*clock=*/"clk2", MulticlockJoin::kSingleDelay, /*admits_empty=*/true},
      {/*clock=*/"clk3", MulticlockJoin::kSingleDelay, /*admits_empty=*/false},
  };
  const std::optional<std::string> kError =
      CheckMulticlockSequenceLegality(kSubsequences);
  ASSERT_TRUE(kError.has_value());
  if (!kError.has_value()) return;
  const std::string& error = *kError;
  EXPECT_FALSE(error.empty());
}

// R2 (§16.13.1): the operator restriction is decided per boundary by the clocks
// actually adjacent at that boundary. Within a sequence that crosses clocks
// overall, a join between two subsequences sharing the same clock stays singly
// clocked and may use an operator other than `##1`/`##0`.
TEST(MulticlockSequenceLegality, SameClockOtherJoinWithinMulticlockIsLegal) {
  const std::vector<MulticlockSubsequence> kSubsequences = {
      {/*clock=*/"clk1", MulticlockJoin::kLeading, /*admits_empty=*/false},
      {/*clock=*/"clk1", MulticlockJoin::kOther, /*admits_empty=*/false},
      {/*clock=*/"clk2", MulticlockJoin::kSingleDelay, /*admits_empty=*/false},
  };
  EXPECT_FALSE(CheckMulticlockSequenceLegality(kSubsequences).has_value());
}

// R1 (§16.13.1): the empty-match restriction applies only once the
// concatenation genuinely spans more than one clock. A chain of several
// subsequences that all share one clock collapses to a singly clocked sequence,
// so an empty-matching subsequence among them stays legal even though the same
// subsequence would be rejected across a clock boundary. Contrasts with
// EmptyMatchingInteriorSubsequenceIsIllegal, which differs only in the clocks.
TEST(MulticlockSequenceLegality, SameClockChainWithEmptyMatchIsLegal) {
  const std::vector<MulticlockSubsequence> kSubsequences = {
      {/*clock=*/"clk", MulticlockJoin::kLeading, /*admits_empty=*/false},
      {/*clock=*/"clk", MulticlockJoin::kSingleDelay, /*admits_empty=*/true},
      {/*clock=*/"clk", MulticlockJoin::kSingleDelay, /*admits_empty=*/false},
  };
  EXPECT_FALSE(CheckMulticlockSequenceLegality(kSubsequences).has_value());
}

// R2 (§16.13.1): conversely, an operator other than `##1`/`##0` at a boundary
// whose adjacent subsequences are differently clocked is illegal even when it
// appears deeper in the chain.
TEST(MulticlockSequenceLegality, CrossClockOtherJoinInInteriorIsIllegal) {
  const std::vector<MulticlockSubsequence> kSubsequences = {
      {/*clock=*/"clk1", MulticlockJoin::kLeading, /*admits_empty=*/false},
      {/*clock=*/"clk2", MulticlockJoin::kSingleDelay, /*admits_empty=*/false},
      {/*clock=*/"clk3", MulticlockJoin::kOther, /*admits_empty=*/false},
  };
  const std::optional<std::string> kError =
      CheckMulticlockSequenceLegality(kSubsequences);
  ASSERT_TRUE(kError.has_value());
  if (!kError.has_value()) return;
  const std::string& error = *kError;
  EXPECT_FALSE(error.empty());
}

}  // namespace
