#include <gtest/gtest.h>

#include <cstdint>
#include <fstream>
#include <string>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

TEST(Coverage, AutoBinSampleAndCoverage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 4;
  CoverageDB::AutoCreateBins(cp, 0, 3);

  db.Sample(g, {{"x", 0}});
  db.Sample(g, {{"x", 1}});
  db.Sample(g, {{"x", 2}});
  db.Sample(g, {{"x", 3}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 100.0);
}

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

TEST(Coverage, CovergroupCoverageIsItemWeightedAverage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");

  auto* full = CoverageDB::AddCoverPoint(g, "full");
  full->weight = 3;
  CoverBin fb;
  fb.name = "b0";
  fb.values = {0};
  CoverageDB::AddBin(full, fb);

  auto* empty = CoverageDB::AddCoverPoint(g, "empty");
  empty->weight = 1;
  CoverBin eb;
  eb.name = "b0";
  eb.values = {0};
  CoverageDB::AddBin(empty, eb);

  db.Sample(g, {{"full", 0}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g), 75.0);
}

TEST(Coverage, CovergroupCoverageWeightsCrossItems) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");

  auto* cp = CoverageDB::AddCoverPoint(g, "z");
  cp->weight = 1;
  CoverBin zb;
  zb.name = "b0";
  zb.values = {0};
  CoverageDB::AddBin(cp, zb);

  CrossCover cross;
  cross.name = "xy";
  cross.coverpoint_names = {"x", "y"};
  cross.option.weight = 3;
  CrossBin cb;
  cb.name = "<0,0>";
  cb.value_sets = {{0}, {0}};
  cross.bins.push_back(cb);
  CoverageDB::AddCross(g, std::move(cross));

  db.Sample(g, {{"x", 0}, {"y", 0}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g), 75.0);
}

TEST(Coverage, ExcludedItemDropsFromBothNumeratorAndDenominator) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");

  auto* keep = CoverageDB::AddCoverPoint(g, "keep");
  CoverBin kb;
  kb.name = "b0";
  kb.values = {0};
  CoverageDB::AddBin(keep, kb);

  auto* drop = CoverageDB::AddCoverPoint(g, "drop");
  CoverBin db0;
  db0.name = "b0";
  db0.values = {0};
  CoverageDB::AddBin(drop, db0);
  drop->excluded_from_coverage = true;

  db.Sample(g, {{"keep", 0}});

  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g), 100.0);
}

TEST(Coverage, AllItemWeightsZeroMakesDenominatorZero) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->weight = 0;
  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);

  db.Sample(g, {{"x", 0}});

  EXPECT_TRUE(CoverageDB::CovergroupCoverageDenominatorZero(g));
}

TEST(Coverage, AllItemsExcludedMakesDenominatorZero) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);
  cp->excluded_from_coverage = true;

  db.Sample(g, {{"x", 0}});

  EXPECT_TRUE(CoverageDB::CovergroupCoverageDenominatorZero(g));
}

TEST(Coverage, NoItemsMakesDenominatorZero) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");

  EXPECT_TRUE(CoverageDB::CovergroupCoverageDenominatorZero(g));
}

TEST(Coverage, ZeroDenominatorZeroWeightCovergroupReports100) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  g->options.weight = 0;

  EXPECT_DOUBLE_EQ(CoverageDB::GetCoverage(g), 100.0);
}

TEST(Coverage, ZeroDenominatorTwoArgFormReportsZeroCounts) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->weight = 0;
  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);

  db.Sample(g, {{"x", 0}});

  int32_t covered = -1;
  int32_t total = -1;
  CoverageDB::GetCoverage(g, covered, total);
  EXPECT_EQ(covered, 0);
  EXPECT_EQ(total, 0);
}

TEST(Coverage, GetCoverageSyscallNoInstancesReturns100) {
  const std::string kSrc =
      "module t;\n"
      "  real cov;\n"
      "  initial cov = $get_coverage();\n"
      "endmodule\n";
  EXPECT_DOUBLE_EQ(RunAndGetReal(kSrc, "cov"), 100.0);
}

TEST(Coverage, OverallCoverageSkipsZeroDenominatorCovergroups) {
  CoverageDB db;
  auto* good = db.CreateGroup("good");
  auto* cp = CoverageDB::AddCoverPoint(good, "x");
  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);
  db.Sample(good, {{"x", 0}});

  db.CreateGroup("empty");

  EXPECT_DOUBLE_EQ(db.GetGlobalCoverage(), 100.0);
}

TEST(Coverage, OverallCoverageAllZeroWeightIs100) {
  CoverageDB db;
  auto* g = db.CreateGroup("g");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);
  db.Sample(g, {{"x", 0}});
  g->options.weight = 0;

  EXPECT_DOUBLE_EQ(db.GetGlobalCoverage(), 100.0);
}

TEST(Coverage, GetCoverageSyscallAveragesCoverpointItemsEndToEnd) {
  std::string path = testing::TempDir() + "delta_cov_19_11_avg.txt";
  {
    std::ofstream out(path);
    out << "CG cg 1\n"
        << "CP full\n"
        << "BIN b0 0 1\n"
        << "BIN b1 1 1\n"
        << "CP empty\n"
        << "BIN c0 0 0\n"
        << "BIN c1 1 0\n";
  }
  const std::string kSrc =
      "module t;\n"
      "  real cov;\n"
      "  initial begin\n"
      "    $load_coverage_db(\"" +
      path +
      "\");\n"
      "    cov = $get_coverage();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_DOUBLE_EQ(RunAndGetReal(kSrc, "cov"), 50.0);
}

TEST(TypeCoverageSim,
     ACovergroupTypesCoverageWeighsItsItemsByTheirTypeWeights) {
  SimFixture f;
  auto out = RunCapture(
      "covergroup gc with function sample(bit a_var, bit b_var);\n"
      "  type_option.merge_instances = 1;\n"
      "  a : coverpoint a_var { type_option.weight = 3; bins one = {1}; }\n"
      "  b : coverpoint b_var { bins one = {1}; }\n"
      "  c : coverpoint b_var { ignore_bins i = {0, 1}; }\n"
      "endgroup\n"
      "covergroup gz with function sample(bit a_var);\n"
      "  type_option.merge_instances = 1;\n"
      "  a : coverpoint a_var { type_option.weight = 0; bins one = {1}; }\n"
      "endgroup\n"
      "covergroup gp with function sample(bit a_var, bit b_var);\n"
      "  type_option.merge_instances = 1;\n"
      "  a : coverpoint a_var { bins one = {1}; }\n"
      "  b : coverpoint b_var { bins one = {1}; }\n"
      "endgroup\n"
      "module t;\n"
      "  initial begin\n"
      "    automatic gc g1 = new;\n"
      "    automatic gp g2 = new;\n"
      "    automatic gz g3 = new;\n"
      "    gp::a::type_option.weight = 3;\n"
      "    g1.sample(0, 1); g2.sample(0, 1); g3.sample(1);\n"
      "    $display(\"%0.2f %0.2f %0.2f\", gc::get_coverage(),\n"
      "             gp::get_coverage(), gz::get_coverage());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "25.00 25.00 0.00\n");
}

}  // namespace
