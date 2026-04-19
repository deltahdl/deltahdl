#include "simulator/specify.h"

#include <gtest/gtest.h>

#include <vector>

using namespace delta;

namespace {

// Build a PathDelay with the given transition slot values. Callers pass the
// values that matter for the test; unspecified slots stay at zero.
PathDelay MakePath(std::string src, std::string dst,
                   std::initializer_list<uint64_t> values) {
  PathDelay pd;
  pd.src_port = std::move(src);
  pd.dst_port = std::move(dst);
  pd.delay_count = static_cast<uint8_t>(values.size());
  size_t i = 0;
  for (uint64_t v : values) pd.delays[i++] = v;
  return pd;
}

// §30.5.3: an empty candidate list has no active path, so the selector has
// nothing to choose from and must report a zero delay.
TEST(SpecifyDelaySelection, NoCandidatesReturnsZero) {
  std::vector<PathCandidate> candidates;
  EXPECT_EQ(SelectPathDelay(candidates, 0), 0u);
}

// §30.5.3: a single candidate whose input has transitioned and whose
// condition is true is active on its own, so its delay must be returned.
TEST(SpecifyDelaySelection, SingleActiveCandidateReturnsItsDelay) {
  PathDelay pd = MakePath("a", "y", {7, 9});
  std::vector<PathCandidate> candidates = {
      {&pd, /*last_transition_time=*/10, /*condition_true=*/true},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 0), 7u);
}

// §30.5.3: a path whose condition evaluates to false is not active, so even
// the lone candidate being false-conditioned must yield a zero result.
TEST(SpecifyDelaySelection, SingleFalseConditionCandidateReturnsZero) {
  PathDelay pd = MakePath("a", "y", {7, 9});
  std::vector<PathCandidate> candidates = {
      {&pd, /*last_transition_time=*/10, /*condition_true=*/false},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 0), 0u);
}

// §30.5.3: among two candidates that transitioned at the same time, a false
// condition disqualifies one of them — even if its delay would otherwise be
// smaller — and the surviving true-conditioned candidate's delay is chosen.
TEST(SpecifyDelaySelection, FalseConditionExcludesOtherwiseSmallerDelay) {
  PathDelay a = MakePath("a", "y", {2, 9});  // smaller but condition false
  PathDelay b = MakePath("b", "y", {8, 9});
  std::vector<PathCandidate> candidates = {
      {&a, /*last_transition_time=*/10, /*condition_true=*/false},
      {&b, /*last_transition_time=*/10, /*condition_true=*/true},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 0), 8u);
}

// §30.5.3: only inputs that transitioned most recently in time are active.
// A candidate whose input transitioned earlier is ignored even if its delay
// is smaller than the most-recent input's delay.
TEST(SpecifyDelaySelection, EarlierInputExcludesSmallerDelay) {
  PathDelay a = MakePath("a", "y", {2, 9});  // earlier, smaller delay
  PathDelay b = MakePath("b", "y", {8, 11});
  std::vector<PathCandidate> candidates = {
      {&a, /*last_transition_time=*/5, /*condition_true=*/true},
      {&b, /*last_transition_time=*/10, /*condition_true=*/true},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 0), 8u);
}

// §30.5.3: simultaneous input transitions keep every corresponding path
// active at the same time, so the selector must pick the smallest delay
// across all of them, not just the first or last candidate.
TEST(SpecifyDelaySelection, SimultaneousInputsSelectSmallestDelay) {
  PathDelay a = MakePath("a", "y", {6, 9});
  PathDelay b = MakePath("b", "y", {5, 11});  // tied time, smaller rise
  std::vector<PathCandidate> candidates = {
      {&a, /*last_transition_time=*/10, /*condition_true=*/true},
      {&b, /*last_transition_time=*/10, /*condition_true=*/true},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 0), 5u);
}

// §30.5.3 Example 1: (A => Y) = (6, 9); (B => Y) = (5, 11). When A
// transitioned more recently than B, the delay chosen for a 0->1 rise is
// A's rise delay of 6.
TEST(SpecifyDelaySelection, LrmExample1AMoreRecentRiseIsSix) {
  PathDelay a = MakePath("a", "y", {6, 9});
  PathDelay b = MakePath("b", "y", {5, 11});
  std::vector<PathCandidate> candidates = {
      {&a, /*last_transition_time=*/20, /*condition_true=*/true},
      {&b, /*last_transition_time=*/10, /*condition_true=*/true},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 0), 6u);
}

// §30.5.3 Example 1: same paths but B transitioned more recently than A,
// so the selector uses B's rise delay of 5 for the 0->1 transition.
TEST(SpecifyDelaySelection, LrmExample1BMoreRecentRiseIsFive) {
  PathDelay a = MakePath("a", "y", {6, 9});
  PathDelay b = MakePath("b", "y", {5, 11});
  std::vector<PathCandidate> candidates = {
      {&a, /*last_transition_time=*/10, /*condition_true=*/true},
      {&b, /*last_transition_time=*/20, /*condition_true=*/true},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 0), 5u);
}

// §30.5.3 Example 1: A and B transition simultaneously; both paths are
// active, and the smallest rise delay across them — 5 from B — is chosen.
TEST(SpecifyDelaySelection, LrmExample1SimultaneousRiseIsFive) {
  PathDelay a = MakePath("a", "y", {6, 9});
  PathDelay b = MakePath("b", "y", {5, 11});
  std::vector<PathCandidate> candidates = {
      {&a, /*last_transition_time=*/15, /*condition_true=*/true},
      {&b, /*last_transition_time=*/15, /*condition_true=*/true},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 0), 5u);
}

// §30.5.3 Example 1: the LRM explicitly names 9 as the 1->0 fall delay
// chosen from A when Y is instead transitioning from 1 to 0 with A as the
// most-recent input.
TEST(SpecifyDelaySelection, LrmExample1AMoreRecentFallIsNine) {
  PathDelay a = MakePath("a", "y", {6, 9});
  PathDelay b = MakePath("b", "y", {5, 11});
  std::vector<PathCandidate> candidates = {
      {&a, /*last_transition_time=*/20, /*condition_true=*/true},
      {&b, /*last_transition_time=*/10, /*condition_true=*/true},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 1), 9u);
}

// §30.5.3: the "specific transition being scheduled" determines which slot
// of delays[] participates in the comparison. Switching the slot from rise
// to fall must change which candidate wins when the ordering flips.
TEST(SpecifyDelaySelection, TransitionSlotPicksCorrectColumn) {
  PathDelay a = MakePath("a", "y", {3, 20});  // small rise, big fall
  PathDelay b = MakePath("b", "y", {20, 3});  // big rise, small fall
  std::vector<PathCandidate> candidates = {
      {&a, /*last_transition_time=*/10, /*condition_true=*/true},
      {&b, /*last_transition_time=*/10, /*condition_true=*/true},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 0), 3u);  // rise slot -> a
  EXPECT_EQ(SelectPathDelay(candidates, 1), 3u);  // fall slot -> b
}

// §30.5.3 Example 2 with MODE==2: the first three guarded paths are active,
// and a rise transition selects the smallest rise delay, which is 4.
TEST(SpecifyDelaySelection, LrmExample2Mode2RiseIsFour) {
  PathDelay p5 = MakePath("a", "y", {5, 9});   // if (MODE < 5)
  PathDelay p4 = MakePath("a", "y", {4, 8});   // if (MODE < 4)
  PathDelay p3 = MakePath("a", "y", {6, 5});   // if (MODE < 3)
  PathDelay p2 = MakePath("a", "y", {3, 2});   // if (MODE < 2)
  PathDelay p1 = MakePath("a", "y", {7, 7});   // if (MODE < 1)
  std::vector<PathCandidate> candidates = {
      {&p5, 10, true},   // MODE==2 < 5 -> true
      {&p4, 10, true},   // MODE==2 < 4 -> true
      {&p3, 10, true},   // MODE==2 < 3 -> true
      {&p2, 10, false},  // MODE==2 < 2 -> false
      {&p1, 10, false},  // MODE==2 < 1 -> false
  };
  EXPECT_EQ(SelectPathDelay(candidates, 0), 4u);
}

// §30.5.3 Example 2 with MODE==2: a fall transition over the same three
// active paths selects the smallest fall delay, which is 5.
TEST(SpecifyDelaySelection, LrmExample2Mode2FallIsFive) {
  PathDelay p5 = MakePath("a", "y", {5, 9});
  PathDelay p4 = MakePath("a", "y", {4, 8});
  PathDelay p3 = MakePath("a", "y", {6, 5});
  PathDelay p2 = MakePath("a", "y", {3, 2});
  PathDelay p1 = MakePath("a", "y", {7, 7});
  std::vector<PathCandidate> candidates = {
      {&p5, 10, true},
      {&p4, 10, true},
      {&p3, 10, true},
      {&p2, 10, false},
      {&p1, 10, false},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 1), 5u);
}

// §30.5.3 Example 2 with MODE==0: every guard evaluates to true, so all
// five paths are active. The smallest rise delay across the five is 3.
TEST(SpecifyDelaySelection, LrmExample2Mode0RiseIsThree) {
  PathDelay p5 = MakePath("a", "y", {5, 9});
  PathDelay p4 = MakePath("a", "y", {4, 8});
  PathDelay p3 = MakePath("a", "y", {6, 5});
  PathDelay p2 = MakePath("a", "y", {3, 2});
  PathDelay p1 = MakePath("a", "y", {7, 7});
  std::vector<PathCandidate> candidates = {
      {&p5, 10, true},
      {&p4, 10, true},
      {&p3, 10, true},
      {&p2, 10, true},
      {&p1, 10, true},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 0), 3u);
}

// §30.5.3 Example 2 with MODE==5: no guard is satisfied (MODE < 5 is false
// and so are all tighter bounds), so no path is active and the selector has
// nothing to return.
TEST(SpecifyDelaySelection, LrmExample2Mode5NoActivePathsReturnsZero) {
  PathDelay p5 = MakePath("a", "y", {5, 9});
  PathDelay p4 = MakePath("a", "y", {4, 8});
  PathDelay p3 = MakePath("a", "y", {6, 5});
  PathDelay p2 = MakePath("a", "y", {3, 2});
  PathDelay p1 = MakePath("a", "y", {7, 7});
  std::vector<PathCandidate> candidates = {
      {&p5, 10, false},
      {&p4, 10, false},
      {&p3, 10, false},
      {&p2, 10, false},
      {&p1, 10, false},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 0), 0u);
}

// §30.5.3: the "most recently transitioned" set is defined by the maximum
// timestamp, not by any particular ordering in the candidate vector. Placing
// the latest-transitioning candidate last must not change the outcome.
TEST(SpecifyDelaySelection, MostRecentIsIndependentOfCandidateOrder) {
  PathDelay a = MakePath("a", "y", {2, 9});   // later but larger delay
  PathDelay b = MakePath("b", "y", {99, 99}); // earlier; must be ignored
  std::vector<PathCandidate> candidates = {
      {&b, /*last_transition_time=*/5, /*condition_true=*/true},
      {&a, /*last_transition_time=*/20, /*condition_true=*/true},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 0), 2u);
}

// §30.5.3: "most recent" includes ties. Three candidates share the maximum
// timestamp, and the smallest of their delays wins — proving the selector
// does not stop at the first tied candidate it encounters.
TEST(SpecifyDelaySelection, SmallestWinsAcrossMultipleTiedCandidates) {
  PathDelay a = MakePath("a", "y", {8});
  PathDelay b = MakePath("b", "y", {5});
  PathDelay c = MakePath("c", "y", {3});
  std::vector<PathCandidate> candidates = {
      {&a, 10, true},
      {&b, 10, true},
      {&c, 10, true},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 0), 3u);
}

}  // namespace
