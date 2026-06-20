#include <gtest/gtest.h>

#include <array>
#include <vector>

#include "simulator/specify.h"

using namespace delta;

namespace {

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

// The LRM Example 2 cases all share the same five paths (p5..p1) and differ
// only in which candidates are active; this builds the five paths in that
// fixed order: {p5, p4, p3, p2, p1}.
std::array<PathDelay, 5> MakeLrmExample2Paths() {
  return {
      MakePath("a", "y", {5, 9}), MakePath("a", "y", {4, 8}),
      MakePath("a", "y", {6, 5}), MakePath("a", "y", {3, 2}),
      MakePath("a", "y", {7, 7}),
  };
}

TEST(SpecifyDelaySelection, NoCandidatesReturnsZero) {
  std::vector<PathCandidate> candidates;
  EXPECT_EQ(SelectPathDelay(candidates, 0), 0u);
}

TEST(SpecifyDelaySelection, SingleActiveCandidateReturnsItsDelay) {
  PathDelay pd = MakePath("a", "y", {7, 9});
  std::vector<PathCandidate> candidates = {
      {&pd, 10, true},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 0), 7u);
}

TEST(SpecifyDelaySelection, LrmExample1AMoreRecentRiseIsSix) {
  PathDelay a = MakePath("a", "y", {6, 9});
  PathDelay b = MakePath("b", "y", {5, 11});
  std::vector<PathCandidate> candidates = {
      {&a, 20, true},
      {&b, 10, true},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 0), 6u);
}

TEST(SpecifyDelaySelection, LrmExample1BMoreRecentRiseIsFive) {
  PathDelay a = MakePath("a", "y", {6, 9});
  PathDelay b = MakePath("b", "y", {5, 11});
  std::vector<PathCandidate> candidates = {
      {&a, 10, true},
      {&b, 20, true},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 0), 5u);
}

TEST(SpecifyDelaySelection, LrmExample1SimultaneousRiseIsFive) {
  PathDelay a = MakePath("a", "y", {6, 9});
  PathDelay b = MakePath("b", "y", {5, 11});
  std::vector<PathCandidate> candidates = {
      {&a, 15, true},
      {&b, 15, true},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 0), 5u);
}

TEST(SpecifyDelaySelection, LrmExample1AMoreRecentFallIsNine) {
  PathDelay a = MakePath("a", "y", {6, 9});
  PathDelay b = MakePath("b", "y", {5, 11});
  std::vector<PathCandidate> candidates = {
      {&a, 20, true},
      {&b, 10, true},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 1), 9u);
}

TEST(SpecifyDelaySelection, LrmExample2Mode2RiseIsFour) {
  std::array<PathDelay, 5> p = MakeLrmExample2Paths();
  std::vector<PathCandidate> candidates = {
      {&p[0], 10, true},  {&p[1], 10, true},  {&p[2], 10, true},
      {&p[3], 10, false}, {&p[4], 10, false},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 0), 4u);
}

TEST(SpecifyDelaySelection, LrmExample2Mode2FallIsFive) {
  std::array<PathDelay, 5> p = MakeLrmExample2Paths();
  std::vector<PathCandidate> candidates = {
      {&p[0], 10, true},  {&p[1], 10, true},  {&p[2], 10, true},
      {&p[3], 10, false}, {&p[4], 10, false},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 1), 5u);
}

TEST(SpecifyDelaySelection, LrmExample2Mode0RiseIsThree) {
  std::array<PathDelay, 5> p = MakeLrmExample2Paths();
  std::vector<PathCandidate> candidates = {
      {&p[0], 10, true}, {&p[1], 10, true}, {&p[2], 10, true},
      {&p[3], 10, true}, {&p[4], 10, true},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 0), 3u);
}

TEST(SpecifyDelaySelection, LrmExample2Mode5NoActivePathsReturnsZero) {
  std::array<PathDelay, 5> p = MakeLrmExample2Paths();
  std::vector<PathCandidate> candidates = {
      {&p[0], 10, false}, {&p[1], 10, false}, {&p[2], 10, false},
      {&p[3], 10, false}, {&p[4], 10, false},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 0), 0u);
}

}  // namespace
