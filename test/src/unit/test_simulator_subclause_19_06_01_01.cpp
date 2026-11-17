#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

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

TEST(Coverage, BinsofUsesTransitionLastValue) {
  CoverBin t = MakeTransitionBin("t", {{1, 2, 3}});
  EXPECT_EQ(CoverageDB::BinsofBinValues(t), (std::vector<int64_t>{3}));

  CoverBin v = MakeValueBin("v", {7, 8});
  EXPECT_EQ(CoverageDB::BinsofBinValues(v), (std::vector<int64_t>{7, 8}));
}

TEST(Coverage, BinsofYieldUsesTransitionLastValueForEachBin) {
  CoverPoint cp;
  cp.name = "cp";
  cp.bins = {MakeValueBin("v", {0}), MakeTransitionBin("t", {{4, 5, 6}})};

  auto all = CoverageDB::BinsofYield(&cp);
  ASSERT_EQ(all.size(), 2u);
  EXPECT_EQ(all[0], (std::vector<int64_t>{0}));
  EXPECT_EQ(all[1], (std::vector<int64_t>{6}));

  auto one = CoverageDB::BinsofYield(&cp, 1);
  ASSERT_EQ(one.size(), 1u);
  EXPECT_EQ(one[0], (std::vector<int64_t>{6}));
}

TEST(Coverage, MultiSequenceTransitionBinYieldsEachLastValue) {
  CoverBin t = MakeTransitionBin("t", {{1, 2}, {5, 9}, {3}});
  EXPECT_EQ(CoverageDB::BinsofBinValues(t), (std::vector<int64_t>{2, 9, 3}));
}

TEST(Coverage, IntersectMatchesTransitionLastValueOnly) {
  CoverPoint cp;
  cp.name = "cp";
  cp.bins = {MakeTransitionBin("t", {{1, 2, 3}})};
  auto bins = CoverageDB::BinsofYield(&cp);

  auto hit = CoverageDB::SelectBinsByIntersect(bins, {3}, false);
  EXPECT_EQ(hit, (std::vector<size_t>{0}));

  auto miss = CoverageDB::SelectBinsByIntersect(bins, {2}, false);
  EXPECT_TRUE(miss.empty());

  auto excl = CoverageDB::SelectBinsByIntersect(bins, {2}, true);
  EXPECT_EQ(excl, (std::vector<size_t>{0}));
}

TEST(Coverage, IntersectMatchesLastValueOfEachTransitionSequence) {
  CoverPoint cp;
  cp.name = "cp";
  cp.bins = {MakeTransitionBin("t", {{1, 2, 3}, {7, 8, 9}})};
  auto bins = CoverageDB::BinsofYield(&cp);

  auto hit_second = CoverageDB::SelectBinsByIntersect(bins, {9}, false);
  EXPECT_EQ(hit_second, (std::vector<size_t>{0}));

  auto hit_first = CoverageDB::SelectBinsByIntersect(bins, {3}, false);
  EXPECT_EQ(hit_first, (std::vector<size_t>{0}));

  auto miss_start = CoverageDB::SelectBinsByIntersect(bins, {7}, false);
  EXPECT_TRUE(miss_start.empty());
  auto miss_mid = CoverageDB::SelectBinsByIntersect(bins, {8}, false);
  EXPECT_TRUE(miss_mid.empty());
}

TEST(Coverage, EmptyTransitionSequenceYieldsNoValue) {
  CoverBin t = MakeTransitionBin("t", {{}});
  EXPECT_TRUE(CoverageDB::BinsofBinValues(t).empty());
}

TEST(Coverage, MixedEmptyAndNonEmptyTransitionSequences) {
  CoverBin t = MakeTransitionBin("t", {{}, {4, 5}, {}, {7, 8, 9}});
  EXPECT_EQ(CoverageDB::BinsofBinValues(t), (std::vector<int64_t>{5, 9}));

  CoverPoint cp;
  cp.name = "cp";
  cp.bins = {t};
  auto bins = CoverageDB::BinsofYield(&cp);
  auto hit = CoverageDB::SelectBinsByIntersect(bins, {9}, false);
  EXPECT_EQ(hit, (std::vector<size_t>{0}));
}

TEST(CovergroupInstanceSim,
     BinsofOverATransitionBinFromSourceUsesItsLastValue) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit [1:0] v, w; int n, t;\n"
                 "  covergroup cg;\n"
                 "    cv: coverpoint v { bins tr = (1 => 2 => 3);\n"
                 "      bins z = {0}; }\n"
                 "    cw: coverpoint w { bins w0 = {0}; bins w1 = {1}; }\n"
                 "    xl: cross cv, cw {\n"
                 "      option.cross_retain_auto_bins = 0;\n"
                 "      bins last = binsof(cv) intersect {3};\n"
                 "    }\n"
                 "    xm: cross cv, cw {\n"
                 "      option.cross_retain_auto_bins = 0;\n"
                 "      bins mid = binsof(cv) intersect {2};\n"
                 "    }\n"
                 "  endgroup\n"
                 "  cg c = new;\n"
                 "  initial begin\n"
                 "    w = 1; v = 1; c.sample(); v = 2; c.sample();\n"
                 "    v = 3; c.sample();\n"
                 "    void'(c.xl.get_inst_coverage(n, t));\n"
                 "    $display(\"%0d %0d\", n, t);\n"
                 "    void'(c.xm.get_inst_coverage(n, t));\n"
                 "    $display(\"%0d %0d\", n, t);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "1 1\n0 0\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

}  // namespace
