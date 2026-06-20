#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "simulator/coverage.h"

using namespace delta;

namespace {

TEST(Coverage, GlobalCoverageEmpty) {
  CoverageDB db;
  EXPECT_DOUBLE_EQ(db.GetGlobalCoverage(), 0.0);
}

// LRM 19.9: $set_coverage_db_name(filename) records the file the coverage
// database is written to at the end of a simulation run.
TEST(Coverage, SetCoverageDbNameRecordsTarget) {
  CoverageDB db;
  EXPECT_TRUE(db.CoverageDbName().empty());
  db.SetCoverageDbName("coverage.dat");
  EXPECT_EQ(db.CoverageDbName(), "coverage.dat");
  // A later call replaces the previously recorded target.
  db.SetCoverageDbName("other.dat");
  EXPECT_EQ(db.CoverageDbName(), "other.dat");
}

// LRM 19.9: $get_coverage() returns the overall coverage of all coverage group
// types as a real number in the range 0 to 100.
TEST(Coverage, GetCoverageReturnsRealInRange) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin b0;
  b0.name = "b0";
  b0.values = {0};
  CoverageDB::AddBin(cp, b0);
  CoverBin b1;
  b1.name = "b1";
  b1.values = {1};
  CoverageDB::AddBin(cp, b1);

  db.Sample(g, {{"x", 0}});
  double cov = db.GetGlobalCoverage();
  EXPECT_GE(cov, 0.0);
  EXPECT_LE(cov, 100.0);
  EXPECT_DOUBLE_EQ(cov, 50.0);
}

// LRM 19.9: $load_coverage_db loads cumulative coverage information for all
// coverage group types. Loaded hit counts accumulate onto the live database for
// a covergroup type that already exists.
TEST(Coverage, LoadCumulativeCoverageAccumulatesHits) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin b0;
  b0.name = "b0";
  b0.values = {0};
  CoverageDB::AddBin(cp, b0);
  CoverBin b1;
  b1.name = "b1";
  b1.values = {1};
  CoverageDB::AddBin(cp, b1);

  // Live run only ever sampled b0, so half the bins are covered.
  db.Sample(g, {{"x", 0}});
  EXPECT_DOUBLE_EQ(db.GetGlobalCoverage(), 50.0);

  // A persisted run of the same covergroup type had covered b1.
  CoverGroup loaded;
  loaded.name = "cg";
  loaded.sample_count = 1;
  CoverPoint lcp;
  lcp.name = "x";
  CoverBin lb1;
  lb1.name = "b1";
  lb1.values = {1};
  lb1.hit_count = 1;
  lcp.bins.push_back(lb1);
  loaded.coverpoints.push_back(lcp);

  db.MergeCumulativeCoverage({loaded});

  // The two runs together cover both bins, and the sample counts add up.
  EXPECT_DOUBLE_EQ(db.GetGlobalCoverage(), 100.0);
  EXPECT_EQ(db.FindGroup("cg")->sample_count, 2u);
}

// LRM 19.9: a covergroup type present only in the loaded cumulative coverage is
// added to the database.
TEST(Coverage, LoadCumulativeCoverageAddsAbsentType) {
  CoverageDB db;
  EXPECT_EQ(db.GroupCount(), 0u);

  CoverGroup loaded;
  loaded.name = "cg2";
  loaded.sample_count = 3;
  db.MergeCumulativeCoverage({loaded});

  EXPECT_EQ(db.GroupCount(), 1u);
  ASSERT_NE(db.FindGroup("cg2"), nullptr);
  EXPECT_EQ(db.FindGroup("cg2")->sample_count, 3u);
}

// LRM 19.9 edge case: $get_coverage() reports 100 when every bin of every
// coverage group type is covered.
TEST(Coverage, GetCoverageFullyCoveredReturns100) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin b0;
  b0.name = "b0";
  b0.values = {0};
  CoverageDB::AddBin(cp, b0);
  CoverBin b1;
  b1.name = "b1";
  b1.values = {1};
  CoverageDB::AddBin(cp, b1);

  db.Sample(g, {{"x", 0}});
  db.Sample(g, {{"x", 1}});
  EXPECT_DOUBLE_EQ(db.GetGlobalCoverage(), 100.0);
}

// LRM 19.9 edge case: loading an empty cumulative set leaves the database
// untouched.
TEST(Coverage, LoadCumulativeCoverageEmptyIsNoOp) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  CoverageDB::AddCoverPoint(g, "x");
  g->sample_count = 5;

  db.MergeCumulativeCoverage({});

  EXPECT_EQ(db.GroupCount(), 1u);
  EXPECT_EQ(db.FindGroup("cg")->sample_count, 5u);
}

// LRM 19.9: a coverpoint present only in the loaded cumulative coverage is
// appended to the matching live covergroup type.
TEST(Coverage, LoadCumulativeCoverageAppendsNewCoverpoint) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  CoverageDB::AddCoverPoint(g, "x");

  CoverGroup loaded;
  loaded.name = "cg";
  CoverPoint lcp;
  lcp.name = "y";
  CoverBin lb;
  lb.name = "yb0";
  lb.values = {0};
  lb.hit_count = 1;
  lcp.bins.push_back(lb);
  loaded.coverpoints.push_back(lcp);

  db.MergeCumulativeCoverage({loaded});

  auto* live = db.FindGroup("cg");
  ASSERT_EQ(live->coverpoints.size(), 2u);
  EXPECT_EQ(live->coverpoints[1].name, "y");
  EXPECT_EQ(live->coverpoints[1].bins.at(0).hit_count, 1u);
}

// LRM 19.9: a bin present only in the loaded cumulative coverage is appended to
// the matching live coverpoint rather than merged into an existing bin.
TEST(Coverage, LoadCumulativeCoverageAppendsNewBin) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin b0;
  b0.name = "b0";
  b0.values = {0};
  CoverageDB::AddBin(cp, b0);

  CoverGroup loaded;
  loaded.name = "cg";
  CoverPoint lcp;
  lcp.name = "x";
  CoverBin lb;
  lb.name = "bnew";
  lb.values = {7};
  lb.hit_count = 2;
  lcp.bins.push_back(lb);
  loaded.coverpoints.push_back(lcp);

  db.MergeCumulativeCoverage({loaded});

  auto& bins = db.FindGroup("cg")->coverpoints.at(0).bins;
  ASSERT_EQ(bins.size(), 2u);
  EXPECT_EQ(bins[0].name, "b0");
  EXPECT_EQ(bins[1].name, "bnew");
  EXPECT_EQ(bins[1].hit_count, 2u);
}

// LRM 19.9: cross coverage is also part of the cumulative coverage. Loaded
// cross-bin hit counts accumulate onto a matching live cross, and a cross seen
// only in the loaded data is appended.
TEST(Coverage, LoadCumulativeCoverageMergesCrosses) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  CrossCover live_cross;
  live_cross.name = "xy";
  CrossBin live_bin;
  live_bin.name = "cb";
  live_bin.hit_count = 1;
  live_cross.bins.push_back(live_bin);
  CoverageDB::AddCross(g, live_cross);

  CoverGroup loaded;
  loaded.name = "cg";
  CrossCover loaded_match;
  loaded_match.name = "xy";
  CrossBin loaded_bin;
  loaded_bin.name = "cb";
  loaded_bin.hit_count = 4;
  loaded_match.bins.push_back(loaded_bin);
  loaded.crosses.push_back(loaded_match);
  CrossCover loaded_new;
  loaded_new.name = "zw";
  loaded.crosses.push_back(loaded_new);

  db.MergeCumulativeCoverage({loaded});

  auto& crosses = db.FindGroup("cg")->crosses;
  ASSERT_EQ(crosses.size(), 2u);
  EXPECT_EQ(crosses[0].name, "xy");
  EXPECT_EQ(crosses[0].bins.at(0).hit_count, 5u);
  EXPECT_EQ(crosses[1].name, "zw");
}

// LRM 19.9: $get_coverage() reports the overall coverage of *all* coverage
// group types, so its value aggregates across more than one covergroup type. A
// fully covered type and a half-covered type of equal weight average to 75.
TEST(Coverage, GetCoverageAggregatesAcrossTypes) {
  CoverageDB db;

  auto* a = db.CreateGroup("cg_a");
  auto* acp = CoverageDB::AddCoverPoint(a, "x");
  CoverBin ab0;
  ab0.name = "b0";
  ab0.values = {0};
  CoverageDB::AddBin(acp, ab0);
  CoverBin ab1;
  ab1.name = "b1";
  ab1.values = {1};
  CoverageDB::AddBin(acp, ab1);
  db.Sample(a, {{"x", 0}});
  db.Sample(a, {{"x", 1}});  // both bins hit -> cg_a is 100% covered

  auto* b = db.CreateGroup("cg_b");
  auto* bcp = CoverageDB::AddCoverPoint(b, "y");
  CoverBin bb0;
  bb0.name = "b0";
  bb0.values = {0};
  CoverageDB::AddBin(bcp, bb0);
  CoverBin bb1;
  bb1.name = "b1";
  bb1.values = {1};
  CoverageDB::AddBin(bcp, bb1);
  db.Sample(b, {{"y", 0}});  // only one of two bins hit -> cg_b is 50% covered

  // Overall coverage spans both types: (100 + 50) / 2 with equal weights.
  EXPECT_DOUBLE_EQ(db.GetGlobalCoverage(), 75.0);
}

// LRM 19.9: $load_coverage_db loads cumulative coverage for all coverage group
// types, so a single load can touch more than one type at once.
TEST(Coverage, LoadCumulativeCoverageHandlesMultipleTypes) {
  CoverageDB db;
  auto* a = db.CreateGroup("cg_a");
  a->sample_count = 1;
  auto* b = db.CreateGroup("cg_b");
  b->sample_count = 2;

  CoverGroup la;
  la.name = "cg_a";
  la.sample_count = 10;
  CoverGroup lb;
  lb.name = "cg_b";
  lb.sample_count = 20;
  db.MergeCumulativeCoverage({la, lb});

  EXPECT_EQ(db.FindGroup("cg_a")->sample_count, 11u);
  EXPECT_EQ(db.FindGroup("cg_b")->sample_count, 22u);
}

}  // namespace
