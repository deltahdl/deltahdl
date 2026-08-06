#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "simulator/coverage.h"

using namespace delta;

namespace {

// §19.5.6: a transition bin "0 => 1" is hit only by a completed value
// transition -- the coverpoint must be sampled at 0 and then at 1 on the next
// sample. A lone scalar sample of either endpoint value does not complete the
// sequence, so the transition bin is not matched.
TEST(Coverage, TransitionBinNotMatchedByScalar) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "sig");
  CoverBin tbin;
  tbin.name = "t_01";
  tbin.kind = CoverBinKind::kTransition;
  tbin.transitions = {{0, 1}};
  CoverageDB::AddBin(cp, tbin);

  // A single scalar sample equal to the transition's destination does not, on
  // its own, complete the 0 => 1 sequence.
  db.Sample(g, {{"sig", 1}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 0u);
}

// LRM 19.5.4: "wildcard bins g12_15 = { 4'b11?? };" matches 12 through 15. The
// two '?' bits are wildcards for 0 and 1; the high two bits are fixed at 11.
TEST(Coverage, WildcardValueExpandsToContiguousGroup) {
  auto values = CoverageDB::ExpandWildcardValue(/*pattern=*/0b1100,
                                                /*care_mask=*/0b1100,
                                                /*width=*/4);
  EXPECT_EQ(values, (std::vector<int64_t>{12, 13, 14, 15}));
}

// LRM 19.5.4: only the marked-fixed bits constrain the match. A pattern with no
// fixed bits matches the whole width; a fully fixed pattern matches one value.
TEST(Coverage, WildcardValueFixedAndWildBitExtremes) {
  EXPECT_EQ(CoverageDB::ExpandWildcardValue(0, 0, 2),
            (std::vector<int64_t>{0, 1, 2, 3}));
  EXPECT_EQ(CoverageDB::ExpandWildcardValue(0b101, 0b111, 3),
            (std::vector<int64_t>{5}));
}

// LRM 19.5.4: a wildcard position matches both 0 and 1 regardless of any value
// the pattern happens to carry there, so only the fixed (care_mask) bits affect
// the result. A pattern of 4'b1111 with the low two bits marked wildcard still
// expands to 12..15, identical to 4'b11??.
TEST(Coverage, WildcardValueIgnoresBitsInWildcardPositions) {
  EXPECT_EQ(CoverageDB::ExpandWildcardValue(0b1111, 0b1100, 4),
            (std::vector<int64_t>{12, 13, 14, 15}));
}

// Edge case: a degenerate zero-width pattern denotes no coverage point value,
// so the wildcard expansion yields no matching values at all.
TEST(Coverage, WildcardValueZeroWidthYieldsNothing) {
  EXPECT_TRUE(CoverageDB::ExpandWildcardValue(0, 0, 0).empty());
}

// LRM 19.5.4: a single wildcard bin's count is incremented for every value in
// the matched group. The expanded values flow through the ordinary value-bin
// matching path.
TEST(Coverage, WildcardSingleBinCountsEveryMatch) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "v");
  CoverBin bin;
  bin.name = "g12_15";
  bin.kind = CoverBinKind::kWildcard;
  bin.values = CoverageDB::ExpandWildcardValue(0b1100, 0b1100, 4);
  CoverageDB::AddBin(cp, bin);

  db.Sample(g, {{"v", 13}});
  db.Sample(g, {{"v", 15}});
  db.Sample(g, {{"v", 11}});  // 1011 is outside 12..15, no match
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 2u);
}

// LRM 19.5.4: "wildcard bins g12_15_array[] = { 4'b11?? };" creates a separate
// bin for each of the four matched values. The "[]" array machinery splits the
// expanded set one value per bin.
TEST(Coverage, WildcardArrayBinPerValue) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "v");
  auto values = CoverageDB::ExpandWildcardValue(0b1100, 0b1100, 4);
  ASSERT_EQ(values.size(), 4u);
  for (int64_t val : values) {
    CoverBin bin;
    bin.name = "g12_15_array[" + std::to_string(val) + "]";
    bin.kind = CoverBinKind::kWildcard;
    bin.values = {val};
    CoverageDB::AddBin(cp, bin);
  }

  db.Sample(g, {{"v", 14}});
  // Exactly the bin holding 14 increments.
  for (const auto& bin : g->coverpoints[0].bins) {
    uint64_t expect = (bin.values.front() == 14) ? 1u : 0u;
    EXPECT_EQ(bin.hit_count, expect);
  }
}

// LRM 19.5.4: "wildcard bins T0_3 = (2'b0x => 2'b1x);" is incremented as if by
// (0,1 => 2,3): 00=>10, 00=>11, 01=>10, 01=>11. Expanding each wildcard step
// and forming the set transition reproduces those four sequences.
TEST(Coverage, WildcardTransitionExpandsLikeRangeList) {
  auto from = CoverageDB::ExpandWildcardValue(0b00, 0b10, 2);  // 2'b0x -> {0,1}
  auto to = CoverageDB::ExpandWildcardValue(0b10, 0b10, 2);    // 2'b1x -> {2,3}
  EXPECT_EQ(from, (std::vector<int64_t>{0, 1}));
  EXPECT_EQ(to, (std::vector<int64_t>{2, 3}));

  auto transitions = CoverageDB::ExpandSetTransition({from, to});
  EXPECT_EQ(transitions, (std::vector<std::vector<int64_t>>{
                             {0, 2}, {0, 3}, {1, 2}, {1, 3}}));
}

// LRM 19.5.4: a wildcard transition bin built from the expanded steps counts
// when a sampled sequence completes one of its concrete transitions.
TEST(Coverage, WildcardTransitionBinCounts) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "s");
  auto from = CoverageDB::ExpandWildcardValue(0b00, 0b10, 2);
  auto to = CoverageDB::ExpandWildcardValue(0b10, 0b10, 2);
  CoverBin bin;
  bin.name = "T0_3";
  bin.kind = CoverBinKind::kTransition;
  bin.transitions = CoverageDB::ExpandSetTransition({from, to});
  CoverageDB::AddBin(cp, bin);

  db.Sample(g, {{"s", 1}});  // 01
  db.Sample(g, {{"s", 3}});  // 11  -> 01=>11 is one of the matched transitions
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);
}

// LRM 19.5.4: "wildcard bins T0_3_array[] = (2'b0x => 2'b1x);" creates a
// separate bin for each of the four matched transition sequences. The "[]"
// array machinery splits the expanded transition set one sequence per bin.
TEST(Coverage, WildcardTransitionArrayBinPerSequence) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "s");
  auto from = CoverageDB::ExpandWildcardValue(0b00, 0b10, 2);
  auto to = CoverageDB::ExpandWildcardValue(0b10, 0b10, 2);
  auto transitions = CoverageDB::ExpandSetTransition({from, to});
  ASSERT_EQ(transitions.size(), 4u);
  for (const auto& seq : transitions) {
    CoverBin bin;
    bin.name = "T0_3_array";
    bin.kind = CoverBinKind::kTransition;
    bin.transitions = {seq};
    CoverageDB::AddBin(cp, bin);
  }

  db.Sample(g, {{"s", 0}});  // 00
  db.Sample(g, {{"s", 3}});  // 11 -> completes only the 00=>11 (0=>3) sequence
  for (const auto& bin : g->coverpoints[0].bins) {
    bool is_zero_three = bin.transitions.front() == std::vector<int64_t>{0, 3};
    EXPECT_EQ(bin.hit_count, is_zero_three ? 1u : 0u);
  }
}

// LRM 19.5.4: a wildcard bin only considers 2-state values; a sample containing
// x or z is excluded from the comparison.
TEST(Coverage, WildcardExcludesUnknownSamples) {
  EXPECT_TRUE(CoverageDB::WildcardSampleIncluded(false));
  EXPECT_FALSE(CoverageDB::WildcardSampleIncluded(true));
}

// LRM 19.5.4: wildcard specification of coverpoint bins of a real type is not
// allowed.
TEST(Coverage, WildcardBinsForbiddenOnRealCoverpoint) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* integral_cp = CoverageDB::AddCoverPoint(g, "i");
  auto* real_cp = CoverageDB::AddCoverPoint(g, "r");
  real_cp->is_real = true;
  EXPECT_TRUE(CoverageDB::WildcardBinsAllowed(integral_cp));
  EXPECT_FALSE(CoverageDB::WildcardBinsAllowed(real_cp));
}

}  // namespace
