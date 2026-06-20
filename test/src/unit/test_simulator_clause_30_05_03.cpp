#include <gtest/gtest.h>

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
  PathDelay p5 = MakePath("a", "y", {5, 9});
  PathDelay p4 = MakePath("a", "y", {4, 8});
  PathDelay p3 = MakePath("a", "y", {6, 5});
  PathDelay p2 = MakePath("a", "y", {3, 2});
  PathDelay p1 = MakePath("a", "y", {7, 7});
  std::vector<PathCandidate> candidates = {
      {&p5, 10, true},  {&p4, 10, true},  {&p3, 10, true},
      {&p2, 10, false}, {&p1, 10, false},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 0), 4u);
}

TEST(SpecifyDelaySelection, LrmExample2Mode2FallIsFive) {
  PathDelay p5 = MakePath("a", "y", {5, 9});
  PathDelay p4 = MakePath("a", "y", {4, 8});
  PathDelay p3 = MakePath("a", "y", {6, 5});
  PathDelay p2 = MakePath("a", "y", {3, 2});
  PathDelay p1 = MakePath("a", "y", {7, 7});
  std::vector<PathCandidate> candidates = {
      {&p5, 10, true},  {&p4, 10, true},  {&p3, 10, true},
      {&p2, 10, false}, {&p1, 10, false},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 1), 5u);
}

TEST(SpecifyDelaySelection, LrmExample2Mode0RiseIsThree) {
  PathDelay p5 = MakePath("a", "y", {5, 9});
  PathDelay p4 = MakePath("a", "y", {4, 8});
  PathDelay p3 = MakePath("a", "y", {6, 5});
  PathDelay p2 = MakePath("a", "y", {3, 2});
  PathDelay p1 = MakePath("a", "y", {7, 7});
  std::vector<PathCandidate> candidates = {
      {&p5, 10, true}, {&p4, 10, true}, {&p3, 10, true},
      {&p2, 10, true}, {&p1, 10, true},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 0), 3u);
}

TEST(SpecifyDelaySelection, LrmExample2Mode5NoActivePathsReturnsZero) {
  PathDelay p5 = MakePath("a", "y", {5, 9});
  PathDelay p4 = MakePath("a", "y", {4, 8});
  PathDelay p3 = MakePath("a", "y", {6, 5});
  PathDelay p2 = MakePath("a", "y", {3, 2});
  PathDelay p1 = MakePath("a", "y", {7, 7});
  std::vector<PathCandidate> candidates = {
      {&p5, 10, false}, {&p4, 10, false}, {&p3, 10, false},
      {&p2, 10, false}, {&p1, 10, false},
  };
  EXPECT_EQ(SelectPathDelay(candidates, 0), 0u);
}

}  // namespace
