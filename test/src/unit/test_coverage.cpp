#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "simulation/coverage.h"

using namespace delta;

// =============================================================================
// S19.2-19.3: Covergroup definition and instantiation
// =============================================================================

TEST(Coverage, CreateGroupAndFind) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg_addr");
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(g->name, "cg_addr");
  EXPECT_EQ(db.GroupCount(), 1u);
  auto* found = db.FindGroup("cg_addr");
  EXPECT_EQ(found, g);
}

TEST(Coverage, FindNonexistentGroupReturnsNull) {
  CoverageDB db;
  EXPECT_EQ(db.FindGroup("missing"), nullptr);
}

TEST(Coverage, MultipleGroupInstances) {
  CoverageDB db;
  auto* g1 = db.CreateGroup("cg1");
  auto* g2 = db.CreateGroup("cg2");
  EXPECT_EQ(db.GroupCount(), 2u);
  EXPECT_NE(g1, g2);
  EXPECT_EQ(db.FindGroup("cg1")->name, "cg1");
  EXPECT_EQ(db.FindGroup("cg2")->name, "cg2");
}

// =============================================================================
// S19.5: Coverpoint declaration
// =============================================================================

TEST(Coverage, AddCoverPointToGroup) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "addr");
  ASSERT_NE(cp, nullptr);
  EXPECT_EQ(cp->name, "addr");
  EXPECT_EQ(g->coverpoints.size(), 1u);
}

// =============================================================================
// S19.5.1-19.5.3: Explicit bins
// =============================================================================

TEST(Coverage, ExplicitBinCreation) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "addr");
  CoverBin bin;
  bin.name = "low";
  bin.kind = CoverBinKind::kExplicit;
  bin.values = {0, 1, 2, 3};
  auto* b = CoverageDB::AddBin(cp, bin);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->name, "low");
  EXPECT_EQ(b->values.size(), 4u);
}

TEST(Coverage, SampleHitsExplicitBin) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "val");
  CoverBin bin;
  bin.name = "ones";
  bin.values = {1};
  CoverageDB::AddBin(cp, bin);

  db.Sample(g, {{"val", 1}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);

  db.Sample(g, {{"val", 2}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);  // No change.

  db.Sample(g, {{"val", 1}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 2u);
}

// =============================================================================
// S19.5.1-19.5.3: Auto bins
// =============================================================================

TEST(Coverage, AutoBinCreation) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "addr");
  cp->auto_bin_count = 4;
  CoverageDB::AutoCreateBins(cp, 0, 7);
  EXPECT_EQ(cp->bins.size(), 4u);

  // Each bin should cover 2 values: [0,1], [2,3], [4,5], [6,7].
  EXPECT_EQ(cp->bins[0].values.size(), 2u);
  EXPECT_EQ(cp->bins[0].values[0], 0);
  EXPECT_EQ(cp->bins[0].values[1], 1);
  EXPECT_EQ(cp->bins[3].values[0], 6);
  EXPECT_EQ(cp->bins[3].values[1], 7);
}

TEST(Coverage, AutoBinSmallRange) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 64;
  CoverageDB::AutoCreateBins(cp, 0, 3);
  // Range is 4, smaller than auto_bin_count=64, so only 4 bins.
  EXPECT_EQ(cp->bins.size(), 4u);
  EXPECT_EQ(cp->bins[0].values.size(), 1u);
  EXPECT_EQ(cp->bins[0].values[0], 0);
}

TEST(Coverage, AutoBinSampleAndCoverage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 4;
  CoverageDB::AutoCreateBins(cp, 0, 3);

  // Hit all bins.
  db.Sample(g, {{"x", 0}});
  db.Sample(g, {{"x", 1}});
  db.Sample(g, {{"x", 2}});
  db.Sample(g, {{"x", 3}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 100.0);
}

// =============================================================================
// S19.5.4: Transition bins
// =============================================================================

TEST(Coverage, TransitionBinNotMatchedByScalar) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "sig");
  CoverBin tbin;
  tbin.name = "t_01";
  tbin.kind = CoverBinKind::kTransition;
  tbin.transitions = {{0, 1}};
  CoverageDB::AddBin(cp, tbin);

  // Scalar sample should not hit transition bins.
  db.Sample(g, {{"sig", 0}});
  db.Sample(g, {{"sig", 1}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 0u);
}

// =============================================================================
// S19.5.5: Wildcard bins
// =============================================================================

TEST(Coverage, WildcardBinMatchesValues) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "data");
  CoverBin wbin;
  wbin.name = "w_even";
  wbin.kind = CoverBinKind::kWildcard;
  wbin.values = {0, 2, 4, 6};  // Even values.
  CoverageDB::AddBin(cp, wbin);

  db.Sample(g, {{"data", 2}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);

  db.Sample(g, {{"data", 3}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);  // Odd, no match.
}

// =============================================================================
// S19.5.6: Illegal bins
// =============================================================================

TEST(Coverage, IllegalBinsNotSampled) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "addr");
  CoverBin ib;
  ib.name = "bad_addr";
  ib.kind = CoverBinKind::kIllegal;
  ib.values = {0xFF};
  CoverageDB::AddBin(cp, ib);

  db.Sample(g, {{"addr", 0xFF}});
  // Illegal bins should not be hit during sampling.
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 0u);
}

TEST(Coverage, IllegalBinsExcludedFromCoverage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin good;
  good.name = "valid";
  good.values = {1};
  CoverageDB::AddBin(cp, good);

  CoverBin bad;
  bad.name = "illegal";
  bad.kind = CoverBinKind::kIllegal;
  bad.values = {0xFF};
  CoverageDB::AddBin(cp, bad);

  db.Sample(g, {{"x", 1}});
  // Only the valid bin counts: 1 covered out of 1.
  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 100.0);
}

// =============================================================================
// S19.5.7: Ignore bins
// =============================================================================

TEST(Coverage, IgnoreBinsNotSampled) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "data");
  CoverBin ign;
  ign.name = "skip_zero";
  ign.kind = CoverBinKind::kIgnore;
  ign.values = {0};
  CoverageDB::AddBin(cp, ign);

  db.Sample(g, {{"data", 0}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 0u);
}

TEST(Coverage, IgnoreBinsExcludedFromCoverage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin good;
  good.name = "valid";
  good.values = {1};
  CoverageDB::AddBin(cp, good);

  CoverBin ign;
  ign.name = "ignored";
  ign.kind = CoverBinKind::kIgnore;
  ign.values = {0};
  CoverageDB::AddBin(cp, ign);

  db.Sample(g, {{"x", 1}});
  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 100.0);
}

// =============================================================================
// S19.6: Cross coverage
// =============================================================================

TEST(Coverage, CrossCoverageCreation) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  CoverageDB::AddCoverPoint(g, "a");
  CoverageDB::AddCoverPoint(g, "b");

  CrossCover cross;
  cross.name = "aXb";
  cross.coverpoint_names = {"a", "b"};

  CrossBin cb;
  cb.name = "a0_b0";
  cb.value_sets = {{0}, {0}};
  cross.bins.push_back(cb);

  cb.name = "a1_b1";
  cb.value_sets = {{1}, {1}};
  cross.bins.push_back(cb);

  CoverageDB::AddCross(g, cross);
  EXPECT_EQ(g->crosses.size(), 1u);
  EXPECT_EQ(g->crosses[0].bins.size(), 2u);
}

TEST(Coverage, CrossCoverageSampling) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  CoverageDB::AddCoverPoint(g, "a");
  CoverageDB::AddCoverPoint(g, "b");

  CrossCover cross;
  cross.name = "aXb";
  cross.coverpoint_names = {"a", "b"};

  CrossBin cb;
  cb.name = "a0_b0";
  cb.value_sets = {{0}, {0}};
  cross.bins.push_back(cb);

  cb.name = "a1_b1";
  cb.value_sets = {{1}, {1}};
  cross.bins.push_back(cb);

  CoverageDB::AddCross(g, cross);

  db.Sample(g, {{"a", 0}, {"b", 0}});
  EXPECT_EQ(g->crosses[0].bins[0].hit_count, 1u);
  EXPECT_EQ(g->crosses[0].bins[1].hit_count, 0u);

  db.Sample(g, {{"a", 1}, {"b", 1}});
  EXPECT_EQ(g->crosses[0].bins[1].hit_count, 1u);
}

// =============================================================================
// S19.6.1: Cross bins coverage computation
// =============================================================================

TEST(Coverage, CrossCoverageComputation) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  CoverageDB::AddCoverPoint(g, "a");
  CoverageDB::AddCoverPoint(g, "b");

  CrossCover cross;
  cross.name = "aXb";
  cross.coverpoint_names = {"a", "b"};
  CrossBin cb;
  cb.name = "a0_b0";
  cb.value_sets = {{0}, {0}};
  cross.bins.push_back(cb);
  cb.name = "a1_b1";
  cb.value_sets = {{1}, {1}};
  cross.bins.push_back(cb);
  CoverageDB::AddCross(g, cross);

  db.Sample(g, {{"a", 0}, {"b", 0}});
  // 1 out of 2 cross bins covered.
  EXPECT_DOUBLE_EQ(CoverageDB::GetCrossCoverage(&g->crosses[0]), 50.0);
}

// =============================================================================
// S19.7: Coverage options: at_least, weight, goal
// =============================================================================

TEST(Coverage, AtLeastOption) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin bin;
  bin.name = "b0";
  bin.values = {0};
  bin.at_least = 3;
  CoverageDB::AddBin(cp, bin);

  db.Sample(g, {{"x", 0}});
  db.Sample(g, {{"x", 0}});
  // 2 hits, at_least=3 => not covered yet.
  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 0.0);

  db.Sample(g, {{"x", 0}});
  // 3 hits, at_least=3 => covered.
  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 100.0);
}

TEST(Coverage, WeightOption) {
  CoverageDB db;
  auto* g1 = db.CreateGroup("cg1");
  g1->options.weight = 2;
  auto* cp1 = CoverageDB::AddCoverPoint(g1, "x");
  CoverBin b1;
  b1.name = "b";
  b1.values = {0};
  CoverageDB::AddBin(cp1, b1);
  db.Sample(g1, {{"x", 0}});  // 100% coverage, weight=2.

  auto* g2 = db.CreateGroup("cg2");
  g2->options.weight = 1;
  auto* cp2 = CoverageDB::AddCoverPoint(g2, "y");
  CoverBin b2;
  b2.name = "b";
  b2.values = {0};
  CoverageDB::AddBin(cp2, b2);
  // 0% coverage, weight=1.

  // Global: (100*2 + 0*1) / (2+1) = 200/3 ~ 66.67.
  double global = db.GetGlobalCoverage();
  EXPECT_NEAR(global, 200.0 / 3.0, 0.01);
}

TEST(Coverage, GoalOption) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  g->options.goal = 90.0;
  EXPECT_DOUBLE_EQ(g->options.goal, 90.0);
}

// =============================================================================
// S19.8: Coverage methods
// =============================================================================

TEST(Coverage, SampleCountIncremented) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  CoverageDB::AddCoverPoint(g, "x");

  EXPECT_EQ(g->sample_count, 0u);
  db.Sample(g, {{"x", 0}});
  EXPECT_EQ(g->sample_count, 1u);
  db.Sample(g, {{"x", 1}});
  EXPECT_EQ(g->sample_count, 2u);
}

TEST(Coverage, GetCoveragePercentage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin b1;
  b1.name = "b0";
  b1.values = {0};
  CoverageDB::AddBin(cp, b1);

  CoverBin b2;
  b2.name = "b1";
  b2.values = {1};
  CoverageDB::AddBin(cp, b2);

  db.Sample(g, {{"x", 0}});
  // 1 of 2 bins covered.
  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g), 50.0);
}

TEST(Coverage, GetInstCoverageMatchesGetCoverage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);

  db.Sample(g, {{"x", 0}});
  EXPECT_DOUBLE_EQ(CoverageDB::GetInstCoverage(g), CoverageDB::GetCoverage(g));
}

// =============================================================================
// S19.9: $get_coverage system function
// =============================================================================

TEST(Coverage, GlobalCoverageEmpty) {
  CoverageDB db;
  EXPECT_DOUBLE_EQ(db.GetGlobalCoverage(), 0.0);
}

TEST(Coverage, GlobalCoverageSingleGroup) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);

  db.Sample(g, {{"x", 0}});
  EXPECT_DOUBLE_EQ(db.GetGlobalCoverage(), 100.0);
}

// =============================================================================
// S19.3: Covergroup in class (CoverGroup is independent, can be embedded)
// =============================================================================

TEST(Coverage, CoverGroupAsClassMember) {
  // Simulates a covergroup embedded in a class: just a struct.
  struct MyClass {
    CoverageDB db;
    CoverGroup* cg = nullptr;
    void init() { cg = db.CreateGroup("cg_in_class"); }
  };
  MyClass obj;
  obj.init();
  ASSERT_NE(obj.cg, nullptr);
  EXPECT_EQ(obj.cg->name, "cg_in_class");
}

// =============================================================================
// S19.5: Coverpoint with iff guard
// =============================================================================

TEST(Coverage, IffGuardBlocksSampling) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->has_iff_guard = true;
  cp->iff_guard_value = false;  // Guard is disabled.

  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);

  db.Sample(g, {{"x", 0}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 0u);  // Blocked by iff.
}

TEST(Coverage, IffGuardAllowsSampling) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->has_iff_guard = true;
  cp->iff_guard_value = true;  // Guard is enabled.

  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);

  db.Sample(g, {{"x", 0}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);
}

// =============================================================================
// S19.7: Auto bin max control
// =============================================================================

TEST(Coverage, AutoBinMaxControl) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  g->options.auto_bin_max = 8;
  auto* cp = CoverageDB::AddCoverPoint(g, "addr");
  // auto_bin_count should inherit from group options.
  EXPECT_EQ(cp->auto_bin_count, 8u);
}

// =============================================================================
// Edge case: empty covergroup coverage
// =============================================================================

TEST(Coverage, EmptyGroupCoverageIsZero) {
  CoverageDB db;
  auto* g = db.CreateGroup("empty");
  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g), 0.0);
}

TEST(Coverage, PointCoverageWithNoBinsIs100) {
  CoverPoint cp;
  cp.name = "empty_cp";
  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(&cp), 100.0);
}

// =============================================================================
// Multiple coverpoints in one group
// =============================================================================

TEST(Coverage, MultipleCoverpointsAveraged) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");

  auto* cp1 = CoverageDB::AddCoverPoint(g, "a");
  CoverBin b1;
  b1.name = "b0";
  b1.values = {0};
  CoverageDB::AddBin(cp1, b1);

  auto* cp2 = CoverageDB::AddCoverPoint(g, "b");
  CoverBin b2;
  b2.name = "b0";
  b2.values = {0};
  CoverageDB::AddBin(cp2, b2);

  // Only cover "a", not "b".
  db.Sample(g, {{"a", 0}, {"b", 99}});
  // a=100%, b=0% => average = 50%.
  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g), 50.0);
}
