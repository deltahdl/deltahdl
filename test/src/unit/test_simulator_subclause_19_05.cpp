#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

TEST(Coverage, AddCoverPointToGroup) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "addr");
  ASSERT_NE(cp, nullptr);
  EXPECT_EQ(cp->name, "addr");
  EXPECT_EQ(g->coverpoints.size(), 1u);
}

TEST(Coverage, IffGuardBlocksSampling) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->has_iff_guard = true;
  cp->iff_guard_value = false;

  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);

  db.Sample(g, {{"x", 0}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 0u);
}

TEST(Coverage, IffGuardAllowsSampling) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");
  cp->has_iff_guard = true;
  cp->iff_guard_value = true;

  CoverBin b;
  b.name = "b0";
  b.values = {0};
  CoverageDB::AddBin(cp, b);

  db.Sample(g, {{"x", 0}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);
}

TEST(Coverage, ValueBinCountIncrementsOnEachMatch) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin b;
  b.name = "set";
  b.values = {0, 1, 2};
  CoverageDB::AddBin(cp, b);

  db.Sample(g, {{"x", 1}});
  db.Sample(g, {{"x", 2}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 2u);
}

TEST(Coverage, ValueBinCountUnchangedOnMiss) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin b;
  b.name = "set";
  b.values = {0, 1, 2};
  CoverageDB::AddBin(cp, b);

  db.Sample(g, {{"x", 9}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 0u);
}

TEST(Coverage, TransitionBinCountsOnSequenceMatch) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin t;
  t.name = "t01";
  t.kind = CoverBinKind::kTransition;
  t.transitions = {{0, 1}};
  CoverageDB::AddBin(cp, t);

  db.Sample(g, {{"x", 0}});
  db.Sample(g, {{"x", 1}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);
}

TEST(Coverage, TransitionBinDoesNotCountWithoutSequence) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin t;
  t.name = "t01";
  t.kind = CoverBinKind::kTransition;
  t.transitions = {{0, 1}};
  CoverageDB::AddBin(cp, t);

  db.Sample(g, {{"x", 0}});
  db.Sample(g, {{"x", 2}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 0u);
}

TEST(Coverage, TransitionBinCountsOnMultiStepSequence) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin t;
  t.name = "t012";
  t.kind = CoverBinKind::kTransition;
  t.transitions = {{0, 1, 2}};
  CoverageDB::AddBin(cp, t);

  db.Sample(g, {{"x", 0}});
  db.Sample(g, {{"x", 1}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 0u);
  db.Sample(g, {{"x", 2}});
  EXPECT_EQ(g->coverpoints[0].bins[0].hit_count, 1u);
}

TEST(Coverage, DefaultBinCatchesUnmatchedValue) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin defined;
  defined.name = "lo";
  defined.values = {0, 1};
  CoverageDB::AddBin(cp, defined);

  CoverBin def;
  def.name = "others";
  def.kind = CoverBinKind::kDefault;
  CoverageDB::AddBin(cp, def);

  db.Sample(g, {{"x", 7}});
  EXPECT_EQ(g->coverpoints[0].bins[1].hit_count, 1u);
}

TEST(Coverage, DefaultBinSkipsDefinedValue) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin defined;
  defined.name = "lo";
  defined.values = {0, 1};
  CoverageDB::AddBin(cp, defined);

  CoverBin def;
  def.name = "others";
  def.kind = CoverBinKind::kDefault;
  CoverageDB::AddBin(cp, def);

  db.Sample(g, {{"x", 0}});
  EXPECT_EQ(g->coverpoints[0].bins[1].hit_count, 0u);
}

TEST(Coverage, AutoBinMaxControlsAutoBinCount) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  g->options.auto_bin_max = 4;
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverageDB::AutoCreateBins(cp, 0, 15);
  EXPECT_EQ(cp->bins.size(), 4u);
}

TEST(Coverage, AutoBinsAreMarkedAuto) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  g->options.auto_bin_max = 4;
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverageDB::AutoCreateBins(cp, 0, 15);
  EXPECT_EQ(cp->bins[0].kind, CoverBinKind::kAuto);
}

TEST(Coverage, NoAutoBinsForRealCoverpoint) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  g->options.auto_bin_max = 8;
  auto* cp = CoverageDB::AddCoverPoint(g, "r");
  cp->is_real = true;

  EXPECT_FALSE(CoverageDB::AutoBinsAllowed(cp));
  CoverageDB::AutoCreateBins(cp, 0, 15);
  EXPECT_TRUE(cp->bins.empty());
}

TEST(Coverage, DefaultBinExcludedFromCoverage) {
  CoverageDB db;
  auto* g = db.CreateGroup("cg");
  auto* cp = CoverageDB::AddCoverPoint(g, "x");

  CoverBin defined;
  defined.name = "lo";
  defined.values = {0};
  CoverageDB::AddBin(cp, defined);

  CoverBin def;
  def.name = "others";
  def.kind = CoverBinKind::kDefault;
  CoverageDB::AddBin(cp, def);

  db.Sample(g, {{"x", 0}});
  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(&g->coverpoints[0]), 100.0);
}

TEST(CovergroupInstanceSim, DefaultBinFromDeclarationNotCounted) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] v; int n, t;\n"
                       "  covergroup cg;\n"
                       "    coverpoint v { bins a = {0}; bins b = {1}; bins "
                       "others = default; }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    v = 2; c.sample();\n"
                       "    void'(c.get_inst_coverage(n, t));\n"
                       "    $display(\"n=%0d t=%0d\", n, t);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=0 t=2\n");
}

TEST(CovergroupInstanceSim, CoverpointDataTypeConvertsTheSample) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  bit [7:0] v; int n, t;\n"
          "  covergroup cg;\n"
          "    bit [1:0] lo2: coverpoint v;\n"
          "  endgroup\n"
          "  cg c = new;\n"
          "  initial begin v = 8'h05; c.sample(); void'(c.get_inst_coverage(n, "
          "t)); $display(\"n=%0d t=%0d\", n, t); end\n"
          "endmodule\n",
          f),
      "n=1 t=4\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, CoverpointDataTypeWidensTheExpression) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  bit [1:0] a, b;\n"
          "  covergroup cg;\n"
          "    bit [2:0] cp: coverpoint a + b { bins f = {4}; bins s = {5}; }\n"
          "  endgroup\n"
          "  cg c = new;\n"
          "  initial begin\n"
          "    a = 3; b = 1; c.sample();\n"
          "    $display(\"cov=%0.2f\", c.get_inst_coverage());\n"
          "  end\n"
          "endmodule\n",
          f),
      "cov=50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, CoverpointIffGuardIgnoresSample) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit [1:0] v; bit en;\n"
                 "  covergroup cg;\n"
                 "    coverpoint v iff (en) { bins lo = {0}; bins hi = {3}; }\n"
                 "  endgroup\n"
                 "  cg c = new;\n"
                 "  initial begin\n"
                 "    en = 0; v = 0; c.sample();\n"
                 "    en = 1; v = 3; c.sample();\n"
                 "    $display(\"cov=%0.2f\", c.get_inst_coverage());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "cov=50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

TEST(CovergroupInstanceSim, BinsReadTheGenerateBlockGenvar) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  bit [1:0] v = 1;\n"
          "  for (genvar g = 1; g <= 2; g++) begin : G\n"
          "    covergroup cg; coverpoint v { bins b[] = {[1:g]}; } endgroup\n"
          "    cg c = new;\n"
          "  end\n"
          "  initial begin\n"
          "    G[1].c.sample(); G[2].c.sample();\n"
          "    $display(\"%0.2f %0.2f\", G[1].c.get_inst_coverage(),\n"
          "             G[2].c.get_inst_coverage());\n"
          "  end\n"
          "endmodule\n",
          f),
      "100.00 50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

std::string SimOk(const std::string& src) {
  SimFixture f;
  const std::string kOut = RunCapture(src, f);
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
  return kOut;
}

TEST(CovergroupInstanceSim, AnImplicitDataTypeConvertsTheSample) {
  EXPECT_EQ(SimOk("module top;\n"
                  "  bit [7:0] v; int n, t;\n"
                  "  covergroup cg;\n"
                  "    [1:0] lo: coverpoint v;\n"
                  "  endgroup\n"
                  "  cg c = new;\n"
                  "  initial begin\n"
                  "    v = 8'h05; c.sample();\n"
                  "    void'(c.get_inst_coverage(n, t));\n"
                  "    $display(\"n=%0d t=%0d\", n, t);\n"
                  "  end\n"
                  "endmodule\n"),
            "n=1 t=4\n");
}

TEST(CovergroupInstanceSim, AnIntDataTypeOverARealSamplesTheConvertedValue) {
  EXPECT_EQ(
      SimOk("module top;\n"
            "  real r;\n"
            "  covergroup cg;\n"
            "    int ic: coverpoint r { bins one = {1}; bins two = {2}; }\n"
            "  endgroup\n"
            "  cg c = new;\n"
            "  initial begin\n"
            "    r = 1.4; c.sample();\n"
            "    $display(\"%0.2f\", c.get_inst_coverage());\n"
            "  end\n"
            "endmodule\n"),
      "50.00\n");
}

const char* const kVif =
    "interface ifc;\n"
    "  logic [1:0] v;\n"
    "  logic en;\n"
    "endinterface\n"
    "class C;\n"
    "  virtual ifc w;\n"
    "  bit x;\n";

const char* const kVifTop =
    "module top;\n"
    "  ifc u();\n"
    "  initial begin\n"
    "    static C o = new(u);\n";

TEST(CovergroupInstanceSim, ACoverpointReadsAVirtualInterfaceMember) {
  EXPECT_EQ(SimOk(std::string(kVif) +
                  "  covergroup cg;\n"
                  "    coverpoint w.v { bins a = {1}; bins b = {3}; }\n"
                  "  endgroup\n"
                  "  function new(virtual ifc h); w = h; cg = new; "
                  "endfunction\n"
                  "endclass\n" +
                  kVifTop +
                  "    u.v = 3; o.cg.sample();\n"
                  "    $display(\"%0.2f\", o.cg.get_inst_coverage());\n"
                  "  end\n"
                  "endmodule\n"),
            "50.00\n");
}

TEST(CovergroupInstanceSim, AnIffGuardReadsAVirtualInterfaceMember) {
  EXPECT_EQ(
      SimOk(std::string(kVif) +
            "  covergroup cg;\n"
            "    coverpoint x iff (w.en) { bins z = {0}; bins o = {1}; }\n"
            "  endgroup\n"
            "  function new(virtual ifc h); w = h; cg = new; "
            "endfunction\n"
            "endclass\n" +
            kVifTop +
            "    u.en = 0; o.x = 0; o.cg.sample();\n"
            "    u.en = 1; o.x = 1; o.cg.sample();\n"
            "    $display(\"%0.2f\", o.cg.get_inst_coverage());\n"
            "  end\n"
            "endmodule\n"),
      "50.00\n");
}

std::string ClockedRun(const char* skew, const char* bin) {
  return std::string(
             "module top;\n"
             "  bit clk;\n"
             "  bit [1:0] v;\n"
             "  clocking cb @(posedge clk);\n"
             "    input ") +
         skew +
         " v;\n"
         "  endclocking\n"
         "  covergroup cg;\n"
         "    coverpoint cb.v { " +
         bin +
         " }\n"
         "  endgroup\n"
         "  cg c = new;\n"
         "  initial begin\n"
         "    v = 3;\n"
         "    #5 clk = 1; v = 2;\n"
         "    #1 c.sample();\n"
         "    $display(\"%0.2f\", c.get_inst_coverage());\n"
         "  end\n"
         "endmodule\n";
}

TEST(CovergroupInstanceSim, DISABLED_AStepSkewClockvarSamplesThePreponedValue) {
  EXPECT_EQ(SimOk(ClockedRun("#1step", "bins three = {3};")), "100.00\n");
}

TEST(CovergroupInstanceSim, DISABLED_AZeroSkewClockvarSamplesTheObservedValue) {
  EXPECT_EQ(SimOk(ClockedRun("#0", "bins two = {2};")), "100.00\n");
}

}  // namespace
