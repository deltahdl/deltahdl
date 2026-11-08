#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

TEST(AutoBinCreation, NotAllowedForRealCoverpoint) {
  CoverPoint integral;
  CoverPoint real_cp;
  real_cp.is_real = true;
  EXPECT_TRUE(CoverageDB::AutoBinsAllowed(&integral));
  EXPECT_FALSE(CoverageDB::AutoBinsAllowed(&real_cp));
}

TEST(AutoBinCreation, RealCoverpointGetsNoAutoBins) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "r");
  cp->is_real = true;
  cp->auto_bin_count = 4;

  CoverageDB::AutoCreateBins(cp, 0, 15);
  EXPECT_TRUE(cp->bins.empty());
}

TEST(AutoBinCreation, CountIsMinOfTwoPowMAndAutoBinMax) {
  EXPECT_EQ(CoverageDB::AutoBinCount(8, 64), 64u);
  EXPECT_EQ(CoverageDB::AutoBinCount(2, 64), 4u);
  EXPECT_EQ(CoverageDB::AutoBinCount(6, 64), 64u);
}

TEST(AutoBinCreation, EnumCountIsCardinality) {
  EXPECT_EQ(CoverageDB::AutoBinCountEnum(3), 3u);
  EXPECT_EQ(CoverageDB::AutoBinCountEnum(257), 257u);
}

TEST(AutoBinCreation, BinCountMatchesAutoBinCount) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 4;

  CoverageDB::AutoCreateBins(cp, 0, 3);
  EXPECT_EQ(cp->bins.size(), CoverageDB::AutoBinCount(2, 4));
}

TEST(AutoBinCreation, LastBinAbsorbsRemainder) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 3;

  CoverageDB::AutoCreateBins(cp, 0, 7);

  ASSERT_EQ(cp->bins.size(), 3u);
  EXPECT_EQ(cp->bins[0].ranges, (std::vector<CoverValueRange>{{0, 1}}));
  EXPECT_EQ(cp->bins[1].ranges, (std::vector<CoverValueRange>{{2, 3}}));
  EXPECT_EQ(cp->bins[2].ranges, (std::vector<CoverValueRange>{{4, 7}}));
}

TEST(AutoBinCreation, BinNamesEmbedValueOrRange) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 3;

  CoverageDB::AutoCreateBins(cp, 0, 7);

  ASSERT_EQ(cp->bins.size(), 3u);
  EXPECT_EQ(cp->bins[0].name, "auto[0:1]");
  EXPECT_EQ(cp->bins[1].name, "auto[2:3]");
  EXPECT_EQ(cp->bins[2].name, "auto[4:7]");
}

TEST(AutoBinCreation, SingleValueBinNamesUseTheValue) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 4;

  CoverageDB::AutoCreateBins(cp, 0, 3);

  ASSERT_EQ(cp->bins.size(), 4u);
  EXPECT_EQ(cp->bins[0].name, "auto[0]");
  EXPECT_EQ(cp->bins[3].name, "auto[3]");
}

TEST(AutoBinCreation, EnumBinNameUsesNamedConstant) {
  EXPECT_EQ(CoverageDB::AutoEnumBinName("RED"), "auto[RED]");
}

TEST(AutoBinCreation, SampleWithXZExcluded) {
  EXPECT_TRUE(CoverageDB::AutoBinSampleIncluded(false));
  EXPECT_FALSE(CoverageDB::AutoBinSampleIncluded(true));
}

TEST(AutoBinCreation, EvenDivisionDistributesValuesEqually) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 4;

  CoverageDB::AutoCreateBins(cp, 0, 7);

  ASSERT_EQ(cp->bins.size(), 4u);
  EXPECT_EQ(cp->bins[0].ranges, (std::vector<CoverValueRange>{{0, 1}}));
  EXPECT_EQ(cp->bins[1].ranges, (std::vector<CoverValueRange>{{2, 3}}));
  EXPECT_EQ(cp->bins[2].ranges, (std::vector<CoverValueRange>{{4, 5}}));
  EXPECT_EQ(cp->bins[3].ranges, (std::vector<CoverValueRange>{{6, 7}}));
}

TEST(AutoBinCreation, BinCountClampedToValueCountWhenCapExceedsRange) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 64;

  CoverageDB::AutoCreateBins(cp, 0, 3);

  ASSERT_EQ(cp->bins.size(), 4u);
  EXPECT_EQ(cp->bins[0].ranges, (std::vector<CoverValueRange>{{0, 0}}));
  EXPECT_EQ(cp->bins[3].ranges, (std::vector<CoverValueRange>{{3, 3}}));
}

TEST(AutoBinCreation, WideCoverpointCountCappedByAutoBinMax) {
  EXPECT_EQ(CoverageDB::AutoBinCount(64, 100), 100u);
  EXPECT_EQ(CoverageDB::AutoBinCount(63, 100), 100u);
}

TEST(AutoBinCreation, IgnoreAndIllegalBinsDoNotSuppressAutoBins) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 4;

  CoverBin ignore;
  ignore.kind = CoverBinKind::kIgnore;
  ignore.values = {7, 8};
  CoverageDB::AddBin(cp, ignore);
  CoverBin illegal;
  illegal.kind = CoverBinKind::kIllegal;
  illegal.values = {9};
  CoverageDB::AddBin(cp, illegal);

  EXPECT_TRUE(CoverageDB::ShouldAutoCreateBins(cp));
  CoverageDB::AutoCreateBins(cp, 0, 3);

  int auto_bins = 0;
  for (const auto& b : cp->bins) {
    if (b.kind == CoverBinKind::kAuto) ++auto_bins;
  }
  EXPECT_EQ(auto_bins, 4);
}

TEST(AutoBinCreation, UserDefinedBinSuppressesAutoBins) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->auto_bin_count = 4;

  CoverBin user;
  user.kind = CoverBinKind::kExplicit;
  user.values = {1, 2};
  CoverageDB::AddBin(cp, user);

  EXPECT_FALSE(CoverageDB::ShouldAutoCreateBins(cp));
  CoverageDB::AutoCreateBins(cp, 0, 3);

  ASSERT_EQ(cp->bins.size(), 1u);
  EXPECT_EQ(cp->bins[0].kind, CoverBinKind::kExplicit);
}

TEST(AutoBinCreation, EmptyCoverpointIsEligible) {
  CoverPoint cp;
  EXPECT_TRUE(CoverageDB::ShouldAutoCreateBins(&cp));
}

TEST(AutoBinCreation, RealCoverpointNotEligible) {
  CoverPoint cp;
  cp.is_real = true;
  EXPECT_FALSE(CoverageDB::ShouldAutoCreateBins(&cp));
}

TEST(AutoBinCreation, IgnoreOnlyBinsDoNotSuppressAutoBins) {
  CoverPoint cp;
  CoverBin ignore;
  ignore.kind = CoverBinKind::kIgnore;
  ignore.values = {5};
  cp.bins.push_back(ignore);
  EXPECT_TRUE(CoverageDB::ShouldAutoCreateBins(&cp));
}

TEST(AutoBinCreation, IllegalOnlyBinsDoNotSuppressAutoBins) {
  CoverPoint cp;
  CoverBin illegal;
  illegal.kind = CoverBinKind::kIllegal;
  illegal.values = {5};
  cp.bins.push_back(illegal);
  EXPECT_TRUE(CoverageDB::ShouldAutoCreateBins(&cp));
}

TEST(AutoBinCreation, WildcardBinSuppressesAutoBins) {
  CoverPoint cp;
  CoverBin wildcard;
  wildcard.kind = CoverBinKind::kWildcard;
  wildcard.values = {1};
  cp.bins.push_back(wildcard);
  EXPECT_FALSE(CoverageDB::ShouldAutoCreateBins(&cp));
}

TEST(AutoBinCreation, TransitionBinSuppressesAutoBins) {
  CoverPoint cp;
  CoverBin transition;
  transition.kind = CoverBinKind::kTransition;
  transition.transitions = {{1, 2}};
  cp.bins.push_back(transition);
  EXPECT_FALSE(CoverageDB::ShouldAutoCreateBins(&cp));
}

TEST(AutoBinCreation, DefaultBinSuppressesAutoBins) {
  CoverPoint cp;
  CoverBin dflt;
  dflt.kind = CoverBinKind::kDefault;
  cp.bins.push_back(dflt);
  EXPECT_FALSE(CoverageDB::ShouldAutoCreateBins(&cp));
}

TEST(CovergroupInstanceSim, AutomaticBinsFromDeclaration) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] v; int n, t;\n"
                       "  covergroup cg;\n"
                       "    coverpoint v;\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    v = 0; c.sample();\n"
                       "    v = 2; c.sample();\n"
                       "    void'(c.get_inst_coverage(n, t));\n"
                       "    $display(\"n=%0d t=%0d\", n, t);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=2 t=4\n");
}

TEST(CovergroupInstanceSim, SignedAndExpressionCoverpointsAutomaticBins) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  byte i; bit [1:0] v; int n, t;\n"
                       "  covergroup cg;\n"
                       "    coverpoint i;\n"
                       "    coverpoint v ^ 2'b11;\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    i = -5; v = 0; c.sample();\n"
                       "    void'(c.get_inst_coverage(n, t));\n"
                       "    $display(\"n=%0d t=%0d\", n, t);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=2 t=68\n");
}

TEST(CovergroupInstanceSim, AutomaticBinsOfIntSpanEveryValue) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  int i; int n, t;\n"
          "  covergroup cg;\n"
          "    coverpoint i;\n"
          "  endgroup\n"
          "  cg c = new;\n"
          "  initial begin i = -5; c.sample(); void'(c.get_inst_coverage(n, "
          "t)); $display(\"n=%0d t=%0d\", n, t); end\n"
          "endmodule\n",
          f),
      "n=1 t=64\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, EnumCoverpointGetsOneAutomaticBinPerConstant) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  typedef enum {RED, GREEN, BLUE} color_t;\n"
                       "  color_t col; int n, t;\n"
                       "  covergroup cg; coverpoint col; endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin col = GREEN; c.sample(); "
                       "void'(c.get_inst_coverage(n, t)); $display(\"n=%0d "
                       "t=%0d\", n, t); end\n"
                       "endmodule\n",
                       f),
            "n=1 t=3\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, SampleHoldingUnknownBitsFallsInNoAutomaticBin) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  logic [1:0] v; int n, t;\n"
          "  covergroup cg; coverpoint v; endgroup\n"
          "  cg c = new;\n"
          "  initial begin v = 2'bx0; c.sample(); void'(c.get_inst_coverage(n, "
          "t)); $display(\"n=%0d t=%0d\", n, t); end\n"
          "endmodule\n",
          f),
      "n=0 t=4\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(AutoBinCreationSim, AnEnumDeclaredInAClassHasABinPerValue) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  enum {red, green, blue} color;\n"
      "  typedef enum {A, B} ab_t;\n"
      "  ab_t ab;\n"
      "  int cov, t1, t2, t3;\n"
      "  covergroup cg;\n"
      "    c1: coverpoint color;\n"
      "    c2: coverpoint ab;\n"
      "  endgroup\n"
      "  cg g = new;\n"
      "  class K;\n"
      "    enum {x1, x2, x3, x4} e;\n"
      "    covergroup kg; ce: coverpoint e; endgroup\n"
      "    function new(); kg = new; endfunction\n"
      "  endclass\n"
      "  initial begin\n"
      "    automatic K k = new;\n"
      "    void'(g.c1.get_inst_coverage(cov, t1));\n"
      "    void'(g.c2.get_inst_coverage(cov, t2));\n"
      "    void'(k.kg.ce.get_inst_coverage(cov, t3));\n"
      "    $display(\"%0d %0d %0d\", t1, t2, t3);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 2 4\n");
}

}  // namespace
