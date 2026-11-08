#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_coverage.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

TEST(Coverage, CrossCoverageCreation) {
  CoverageDB db;
  auto* g = SetupTwoPointCross(db);
  EXPECT_EQ(g->crosses.size(), 1u);
  EXPECT_EQ(g->crosses[0].bins.size(), 2u);
}

TEST(Coverage, CrossCoverageSampling) {
  CoverageDB db;
  auto* g = SetupTwoPointCross(db);

  db.Sample(g, {{"a", 0}, {"b", 0}});
  EXPECT_EQ(g->crosses[0].bins[0].hit_count, 1u);
  EXPECT_EQ(g->crosses[0].bins[1].hit_count, 0u);

  db.Sample(g, {{"a", 1}, {"b", 1}});
  EXPECT_EQ(g->crosses[0].bins[1].hit_count, 1u);
}

static CoverPoint* AddPointWithBins(CoverGroup* g, const std::string& name,
                                    const std::vector<int64_t>& bin_values) {
  auto* cp = CoverageDB::AddCoverPoint(g, name);
  for (int64_t v : bin_values) {
    CoverBin b;
    b.name = "b" + std::to_string(v);
    b.values = {v};
    CoverageDB::AddBin(cp, b);
  }
  return cp;
}

TEST(Coverage, CrossCartesianProduct) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  AddPointWithBins(g, "a", {0, 1});
  AddPointWithBins(g, "b", {0, 1, 2});

  CrossCover cross;
  cross.name = "aXb";
  cross.coverpoint_names = {"a", "b"};
  auto* xc = CoverageDB::AddCross(g, std::move(cross));

  CoverageDB::AutoCreateCrossBins(g, xc);
  EXPECT_EQ(xc->bins.size(), 6u);

  db.Sample(g, {{"a", 1}, {"b", 2}});
  uint64_t total_hits = 0;
  for (const auto& cb : xc->bins) total_hits += cb.hit_count;
  EXPECT_EQ(total_hits, 1u);
}

TEST(Coverage, CrossExcludesDefaultIgnoreIllegalBins) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* a = AddPointWithBins(g, "a", {0});
  CoverBin def;
  def.name = "rest";
  def.kind = CoverBinKind::kDefault;
  CoverageDB::AddBin(a, def);
  CoverBin ign;
  ign.name = "skip";
  ign.kind = CoverBinKind::kIgnore;
  ign.values = {9};
  CoverageDB::AddBin(a, ign);

  AddPointWithBins(g, "b", {0, 1});

  CrossCover cross;
  cross.name = "aXb";
  cross.coverpoint_names = {"a", "b"};
  auto* xc = CoverageDB::AddCross(g, std::move(cross));

  CoverageDB::AutoCreateCrossBins(g, xc);
  EXPECT_EQ(xc->bins.size(), 2u);
}

TEST(Coverage, CrossCreatesImplicitCoverpoint) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  AddPointWithBins(g, "a", {0, 1});

  CoverageDB::EnsureCrossCoverPoints(g, {"a", "v"});
  EXPECT_EQ(g->coverpoints.size(), 2u);
  EXPECT_EQ(g->coverpoints.back().name, "v");
}

TEST(Coverage, CrossItemsMustBeInSameGroup) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  AddPointWithBins(g, "a", {0});
  AddPointWithBins(g, "b", {0});

  EXPECT_TRUE(CoverageDB::CrossItemsInSameGroup(g, {"a", "b"}));
  EXPECT_FALSE(CoverageDB::CrossItemsInSameGroup(g, {"a", "elsewhere"}));
}

TEST(Coverage, CrossRejectsBareRealVariable) {
  EXPECT_TRUE(CoverageDB::CrossBareVariableAllowed(false));
  EXPECT_FALSE(CoverageDB::CrossBareVariableAllowed(true));

  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* rp = CoverageDB::AddCoverPoint(g, "rexpr");
  rp->is_real = true;
  EXPECT_TRUE(CoverageDB::CrossItemsInSameGroup(g, {"rexpr"}));
}

TEST(Coverage, CrossIffGuards) {
  CoverageDB db;
  auto* g = SetupTwoPointCross(db);
  auto& cross = g->crosses[0];

  cross.has_iff_guard = true;
  cross.iff_guard_value = false;
  db.Sample(g, {{"a", 0}, {"b", 0}});
  EXPECT_EQ(cross.bins[0].hit_count, 0u);

  cross.iff_guard_value = true;
  cross.bins[0].has_iff_guard = true;
  cross.bins[0].iff_guard_value = false;
  db.Sample(g, {{"a", 0}, {"b", 0}});
  EXPECT_EQ(cross.bins[0].hit_count, 0u);

  cross.bins[0].iff_guard_value = true;
  db.Sample(g, {{"a", 0}, {"b", 0}});
  EXPECT_EQ(cross.bins[0].hit_count, 1u);
}

TEST(Coverage, CrossLabelNamesAndScopesBins) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  AddPointWithBins(g, "a", {0, 1});
  AddPointWithBins(g, "b", {0, 1});

  CrossCover cross;
  cross.name = "aXb";
  cross.coverpoint_names = {"a", "b"};
  auto* xc = CoverageDB::AddCross(g, std::move(cross));
  CoverageDB::AutoCreateCrossBins(g, xc);

  EXPECT_EQ(xc->name, "aXb");
  EXPECT_EQ(g->crosses.size(), 1u);
  EXPECT_EQ(g->crosses[0].name, "aXb");
  EXPECT_FALSE(g->crosses[0].bins.empty());
}

TEST(Coverage, CrossCartesianProductThreeWay) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  AddPointWithBins(g, "a", {0, 1});
  AddPointWithBins(g, "b", {0, 1, 2});
  AddPointWithBins(g, "c", {0, 1});

  CrossCover cross;
  cross.name = "aXbXc";
  cross.coverpoint_names = {"a", "b", "c"};
  auto* xc = CoverageDB::AddCross(g, std::move(cross));
  CoverageDB::AutoCreateCrossBins(g, xc);
  EXPECT_EQ(xc->bins.size(), 12u);
}

TEST(Coverage, CrossEmptyWhenCoverpointHasNoEligibleBins) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* a = CoverageDB::AddCoverPoint(g, "a");
  CoverBin bad;
  bad.name = "bad";
  bad.kind = CoverBinKind::kIllegal;
  bad.values = {0};
  CoverageDB::AddBin(a, bad);
  AddPointWithBins(g, "b", {0, 1});

  CrossCover cross;
  cross.name = "aXb";
  cross.coverpoint_names = {"a", "b"};
  auto* xc = CoverageDB::AddCross(g, std::move(cross));
  CoverageDB::AutoCreateCrossBins(g, xc);
  EXPECT_TRUE(xc->bins.empty());
}

TEST(CovergroupInstanceSim, CrossedVariableGetsImplicitCoverpoint) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] x; bit y; int n, t;\n"
                       "  covergroup cg;\n"
                       "    cx: coverpoint x { bins a = {0}; bins b = {1}; }\n"
                       "    xy: cross cx, y;\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    x = 0; y = 1; c.sample();\n"
                       "    void'(c.get_inst_coverage(n, t));\n"
                       "    $display(\"n=%0d t=%0d\", n, t);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=3 t=8\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
