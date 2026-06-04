#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/coverage.h"

using namespace delta;

namespace {

// Builds a transition bin carrying the given value-transition sequences (each
// inner vector is one ordered sequence, e.g. {1, 2, 3} for 1 => 2 => 3).
CoverBin MakeTransitionBin(const std::string& name,
                           std::vector<std::vector<int64_t>> sequences) {
  CoverBin b;
  b.name = name;
  b.kind = CoverBinKind::kTransition;
  b.transitions = std::move(sequences);
  return b;
}

CoverBin MakeValueBin(const std::string& name, std::vector<int64_t> values) {
  CoverBin b;
  b.name = name;
  b.values = std::move(values);
  return b;
}

// A select expression's binsof on a transition bin intersects against the last
// value of the transition, not its intermediate values (LRM 19.6.1.1).
TEST(Coverage, BinsofUsesTransitionLastValue) {
  CoverBin t = MakeTransitionBin("t", {{1, 2, 3}});
  EXPECT_EQ(CoverageDB::BinsofBinValues(t), (std::vector<int64_t>{3}));

  // An ordinary value bin still contributes its values verbatim.
  CoverBin v = MakeValueBin("v", {7, 8});
  EXPECT_EQ(CoverageDB::BinsofBinValues(v), (std::vector<int64_t>{7, 8}));
}

// binsof(cp) over a coverpoint mixing value and transition bins yields each
// value bin's set and each transition bin's last value (LRM 19.6.1.1).
TEST(Coverage, BinsofYieldUsesTransitionLastValueForEachBin) {
  CoverPoint cp;
  cp.name = "cp";
  cp.bins = {MakeValueBin("v", {0}), MakeTransitionBin("t", {{4, 5, 6}})};

  auto all = CoverageDB::BinsofYield(&cp);
  ASSERT_EQ(all.size(), 2u);
  EXPECT_EQ(all[0], (std::vector<int64_t>{0}));
  EXPECT_EQ(all[1], (std::vector<int64_t>{6}));  // last value of 4 => 5 => 6

  // binsof(cp.bin) on the transition bin alone also yields its last value.
  auto one = CoverageDB::BinsofYield(&cp, 1);
  ASSERT_EQ(one.size(), 1u);
  EXPECT_EQ(one[0], (std::vector<int64_t>{6}));
}

// A transition bin with several sequences contributes the last value of each
// (LRM 19.6.1.1).
TEST(Coverage, MultiSequenceTransitionBinYieldsEachLastValue) {
  CoverBin t = MakeTransitionBin("t", {{1, 2}, {5, 9}, {3}});
  EXPECT_EQ(CoverageDB::BinsofBinValues(t), (std::vector<int64_t>{2, 9, 3}));
}

// End to end: "binsof(t) intersect {y}" selects the transition bin only when y
// overlaps the transition's last value; an intermediate transition value does
// not select it (LRM 19.6.1.1).
TEST(Coverage, IntersectMatchesTransitionLastValueOnly) {
  CoverPoint cp;
  cp.name = "cp";
  cp.bins = {MakeTransitionBin("t", {{1, 2, 3}})};
  auto bins = CoverageDB::BinsofYield(&cp);

  // The last value 3 overlaps -> the bin is selected.
  auto hit = CoverageDB::SelectBinsByIntersect(bins, {3}, /*negate=*/false);
  EXPECT_EQ(hit, (std::vector<size_t>{0}));

  // The intermediate value 2 is not the value binsof uses -> not selected.
  auto miss = CoverageDB::SelectBinsByIntersect(bins, {2}, /*negate=*/false);
  EXPECT_TRUE(miss.empty());

  // The negated form keeps the bin precisely because 2 is not its binsof value.
  auto excl = CoverageDB::SelectBinsByIntersect(bins, {2}, /*negate=*/true);
  EXPECT_EQ(excl, (std::vector<size_t>{0}));
}

// End to end on a multi-sequence transition bin: intersect selects it on the
// last value of any of its sequences, not just the first, and rejects every
// intermediate or starting value of a sequence (LRM 19.6.1.1).
TEST(Coverage, IntersectMatchesLastValueOfEachTransitionSequence) {
  CoverPoint cp;
  cp.name = "cp";
  cp.bins = {MakeTransitionBin("t", {{1, 2, 3}, {7, 8, 9}})};
  auto bins = CoverageDB::BinsofYield(&cp);

  // The last value of the second sequence (9) selects the bin.
  auto hit_second =
      CoverageDB::SelectBinsByIntersect(bins, {9}, /*negate=*/false);
  EXPECT_EQ(hit_second, (std::vector<size_t>{0}));

  // The last value of the first sequence (3) selects it as well.
  auto hit_first = CoverageDB::SelectBinsByIntersect(bins, {3}, /*negate=*/false);
  EXPECT_EQ(hit_first, (std::vector<size_t>{0}));

  // The starting value (7) and an intermediate value (8) of a sequence are not
  // what binsof uses, so neither selects the bin.
  auto miss_start =
      CoverageDB::SelectBinsByIntersect(bins, {7}, /*negate=*/false);
  EXPECT_TRUE(miss_start.empty());
  auto miss_mid = CoverageDB::SelectBinsByIntersect(bins, {8}, /*negate=*/false);
  EXPECT_TRUE(miss_mid.empty());
}

// A transition bin carrying an empty sequence contributes no value, so binsof
// yields an empty set for it (LRM 19.6.1.1).
TEST(Coverage, EmptyTransitionSequenceYieldsNoValue) {
  CoverBin t = MakeTransitionBin("t", {{}});
  EXPECT_TRUE(CoverageDB::BinsofBinValues(t).empty());
}

}
