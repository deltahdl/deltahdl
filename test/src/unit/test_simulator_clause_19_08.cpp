#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "simulator/coverage.h"

using namespace delta;

namespace {

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

// LRM 19.8: stop() halts coverage collection so a subsequent sample() records
// nothing, and start() resumes it.
TEST(Coverage, StartStopControlsCollection) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);

  CoverageDB::Stop(g);
  db.Sample(g, {{"x", 0}});
  EXPECT_EQ(g->sample_count, 0u);
  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g), 0.0);

  CoverageDB::Start(g);
  db.Sample(g, {{"x", 0}});
  EXPECT_EQ(g->sample_count, 1u);
  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g), 100.0);
}

// LRM 19.8: set_inst_name() assigns the instance name procedurally.
TEST(Coverage, SetInstNameStoresName) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  CoverageDB::SetInstName(g, "u_dut");
  EXPECT_EQ(g->options.name, "u_dut");
}

// LRM 19.8: the optional ref-int pair of get_coverage() reports the number of
// covered bins and the number of coverage bins defined for the item.
TEST(Coverage, GetCoverageReportsBinCounts) {
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

  int32_t covered = -1;
  int32_t total = -1;
  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g, covered, total), 50.0);
  EXPECT_EQ(covered, 1);
  EXPECT_EQ(total, 2);
}

// LRM 19.8: the optional ref-int pair of get_inst_coverage() reports, for a
// coverpoint or cross, the numerator and denominator of the coverage value.
TEST(Coverage, GetInstCoverageReportsBinCounts) {
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

  db.Sample(g, {{"x", 1}});

  int32_t covered = -1;
  int32_t total = -1;
  double cov = CoverageDB::GetInstCoverage(g, covered, total);
  EXPECT_DOUBLE_EQ(cov, 50.0);
  EXPECT_EQ(covered, 1);
  EXPECT_EQ(total, 2);
}

// LRM 19.8: when get_coverage()'s ref-int pair is read for a covergroup, the
// counts aggregate the bins of all coverpoints and crosses. Here the only
// coverage item is a cross, so its bins drive the reported totals.
TEST(Coverage, GetCoverageAggregatesCrossBins) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");

  CrossCover cross;
  cross.name = "xy";
  cross.coverpoint_names = {"x", "y"};
  CrossBin cb0;
  cb0.name = "<0,0>";
  cb0.value_sets = {{0}, {0}};
  cross.bins.push_back(cb0);
  CrossBin cb1;
  cb1.name = "<1,1>";
  cb1.value_sets = {{1}, {1}};
  cross.bins.push_back(cb1);
  CoverageDB::AddCross(g, std::move(cross));

  db.Sample(g, {{"x", 0}, {"y", 0}});

  int32_t covered = -1;
  int32_t total = -1;
  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g, covered, total), 50.0);
  EXPECT_EQ(covered, 1);
  EXPECT_EQ(total, 2);
}

// LRM 19.8: get_inst_coverage()'s ref-int pair likewise aggregates cross bins;
// covering both cross bins yields a full count and 100% coverage.
TEST(Coverage, GetInstCoverageAggregatesCrossBins) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");

  CrossCover cross;
  cross.name = "xy";
  cross.coverpoint_names = {"x", "y"};
  CrossBin cb0;
  cb0.name = "<0,0>";
  cb0.value_sets = {{0}, {0}};
  cross.bins.push_back(cb0);
  CrossBin cb1;
  cb1.name = "<1,1>";
  cb1.value_sets = {{1}, {1}};
  cross.bins.push_back(cb1);
  CoverageDB::AddCross(g, std::move(cross));

  db.Sample(g, {{"x", 0}, {"y", 0}});
  db.Sample(g, {{"x", 1}, {"y", 1}});

  int32_t covered = -1;
  int32_t total = -1;
  EXPECT_DOUBLE_EQ(CoverageDB::GetInstCoverage(g, covered, total), 100.0);
  EXPECT_EQ(covered, 2);
  EXPECT_EQ(total, 2);
}

// LRM 19.8 edge case: get_coverage() on a covergroup with no coverage items
// reports zero covered and zero defined bins, and 0% coverage.
TEST(Coverage, GetCoverageEmptyGroupReportsZeroBins) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");

  int32_t covered = -1;
  int32_t total = -1;
  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g, covered, total), 0.0);
  EXPECT_EQ(covered, 0);
  EXPECT_EQ(total, 0);
}

// LRM 19.8 edge case: stop() leaves already-collected coverage intact while
// discarding samples taken while stopped.
TEST(Coverage, StopRetainsCollectedCoverage) {
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
  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g), 50.0);

  CoverageDB::Stop(g);
  db.Sample(g, {{"x", 1}});
  EXPECT_EQ(g->sample_count, 1u);
  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g), 50.0);
}

// LRM 19.8 edge case: a fresh instance collects coverage by default, with no
// preceding start() call required.
TEST(Coverage, DefaultGroupCollectsWithoutStart) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin b0;
  b0.name = "b0";
  b0.values = {0};
  CoverageDB::AddBin(cp, b0);

  db.Sample(g, {{"x", 0}});
  EXPECT_EQ(g->sample_count, 1u);
  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g), 100.0);
}

// LRM 19.8 edge case: a later set_inst_name() replaces an earlier instance
// name.
TEST(Coverage, SetInstNameOverwrites) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  CoverageDB::SetInstName(g, "first");
  CoverageDB::SetInstName(g, "second");
  EXPECT_EQ(g->options.name, "second");
}

}  // namespace
