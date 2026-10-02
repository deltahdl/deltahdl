#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_coverage_point_setup.h"
#include "simulator/coverage.h"
#include "simulator/coverage_types.h"

using namespace delta;

namespace {

// Build a covergroup whose only coverage item is a cross "xy" over coverpoints
// "x" and "y" with two cross bins, <0,0> and <1,1>.
CoverGroup* SetupCrossOnlyGroup(CoverageDB& db) {
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
  return g;
}

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
  auto* g = SetupCrossOnlyGroup(db);

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
  auto* g = SetupCrossOnlyGroup(db);

  db.Sample(g, {{"x", 0}, {"y", 0}});
  db.Sample(g, {{"x", 1}, {"y", 1}});

  int32_t covered = -1;
  int32_t total = -1;
  EXPECT_DOUBLE_EQ(CoverageDB::GetInstCoverage(g, covered, total), 100.0);
  EXPECT_EQ(covered, 2);
  EXPECT_EQ(total, 2);
}

// LRM 19.8: the no-argument form of get_coverage()/get_inst_coverage() may be
// called directly on a coverpoint and returns that item's coverage as a
// percentage; with one of two value bins covered the result is 50%.
TEST(Coverage, GetCoverageOnCoverpointReturnsPercentage) {
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

  EXPECT_DOUBLE_EQ(CoverageDB::GetPointCoverage(cp), 50.0);
}

// LRM 19.8: the no-argument form may likewise be called directly on a cross and
// returns the cross coverage as a percentage; with one of two cross bins hit
// the result is 50%.
TEST(Coverage, GetCoverageOnCrossReturnsPercentage) {
  CoverageDB db;
  auto* g = SetupCrossOnlyGroup(db);

  db.Sample(g, {{"x", 0}, {"y", 0}});

  ASSERT_EQ(g->crosses.size(), 1u);
  EXPECT_DOUBLE_EQ(CoverageDB::GetCrossCoverage(&g->crosses.front()), 50.0);
}

// LRM 19.8: get_coverage()/get_inst_coverage() may be called directly on a
// coverpoint. Its optional ref-int pair then reports the numerator and the
// denominator of the (unscaled) coverage value; with one of two value bins
// covered these are 1 and 2, and the returned percentage is that ratio scaled
// by 100.
TEST(Coverage, GetCoverageOnCoverpointReportsNumeratorDenominator) {
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

  int32_t covered = -1;
  int32_t total = -1;
  double cov = CoverageDB::GetPointCoverage(cp, covered, total);
  EXPECT_EQ(covered, 1);
  EXPECT_EQ(total, 2);
  EXPECT_DOUBLE_EQ(cov, 50.0);
  // The return value is the numerator/denominator ratio scaled by 100.
  EXPECT_DOUBLE_EQ(cov, 100.0 * covered / total);
}

// LRM 19.8: get_coverage()/get_inst_coverage() may likewise be called directly
// on a cross. Its ref-int pair reports the numerator and denominator of the
// cross coverage; with one of two cross bins hit these are 1 and 2 and the
// returned percentage is their ratio scaled by 100.
TEST(Coverage, GetCoverageOnCrossReportsNumeratorDenominator) {
  CoverageDB db;
  auto* g = SetupCrossOnlyGroup(db);

  db.Sample(g, {{"x", 0}, {"y", 0}});

  ASSERT_EQ(g->crosses.size(), 1u);
  const CrossCover& cross = g->crosses.front();
  int32_t covered = -1;
  int32_t total = -1;
  double cov = CoverageDB::GetCrossCoverage(&cross, covered, total);
  EXPECT_EQ(covered, 1);
  EXPECT_EQ(total, 2);
  EXPECT_DOUBLE_EQ(cov, 50.0);
  EXPECT_DOUBLE_EQ(cov, 100.0 * covered / total);
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
  AddTwoValueBinPoint(g);

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

// §19.3 and §19.8: `new` on a covergroup declared in a module builds an
// instance with the declaration's coverpoint and bins, sample() counts the
// coverpoint's value into them, and get_coverage() and get_inst_coverage()
// report the instance, the latter's ref-int pair the covered and defined bins.
// One of the two bins is hit, so each reads 50.
TEST(CovergroupInstanceSim, SampleAndCoverageMethodsOnModuleInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] v; int n, t;\n"
                       "  covergroup cg;\n"
                       "    coverpoint v { bins lo = {0}; bins hi = {3}; }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    v = 0; c.sample();\n"
                       "    v = 1; c.sample();\n"
                       "    $display(\"cov=%0.2f\", c.get_coverage());\n"
                       "    $display(\"inst=%0.2f\", c.get_inst_coverage());\n"
                       "    c.get_inst_coverage(n, t);\n"
                       "    $display(\"n=%0d t=%0d\", n, t);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "cov=50.00\ninst=50.00\nn=1 t=2\n");
}

// §19.8: stop() makes a triggered sample() record nothing until start()
// resumes collection.
TEST(CovergroupInstanceSim, StopAndStartControlCollection) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module top;\n"
                 "  bit [1:0] v;\n"
                 "  covergroup cg;\n"
                 "    coverpoint v { bins lo = {0}; bins hi = {3}; }\n"
                 "  endgroup\n"
                 "  cg c = new;\n"
                 "  initial begin\n"
                 "    c.stop(); v = 0; c.sample();\n"
                 "    $display(\"stopped=%0.2f\", c.get_inst_coverage());\n"
                 "    c.start(); v = 3; c.sample();\n"
                 "    $display(\"started=%0.2f\", c.get_inst_coverage());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "stopped=0.00\nstarted=50.00\n");
}

// §19.8: every coverpoint of an instance has get_inst_coverage(), whose
// ref-int pair receives its covered and defined bins.
TEST(CovergroupInstanceSim, CoverageMethodThroughCoverpoint) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] v; int n, t;\n"
                       "  covergroup cg;\n"
                       "    cp: coverpoint v { bins lo = {0}; bins hi = {3}; "
                       "bins mid = {1}; }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    v = 0; c.sample();\n"
                       "    void'(c.cp.get_inst_coverage(n, t));\n"
                       "    $display(\"n=%0d t=%0d\", n, t);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "n=1 t=3\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// §19.8: get_coverage() called on the covergroup type answers the coverage of
// the type over its instances (§19.11.3), here the one instance's 50.
TEST(CovergroupInstanceSim, TypeCoverageThroughScopeOperator) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] v;\n"
                       "  covergroup cg;\n"
                       "    coverpoint v { bins lo = {0}; bins hi = {3}; }\n"
                       "  endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    v = 0; c.sample();\n"
                       "    $display(\"type=%0.2f\", cg::get_coverage());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "type=50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// §19.8: set_inst_name() sets the instance's name, which §19.10 makes its
// option.name.
TEST(CovergroupInstanceSim, SetInstNameSetsOptionName) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit v;\n"
                       "  covergroup cg; coverpoint v; endgroup\n"
                       "  cg c = new;\n"
                       "  initial begin\n"
                       "    c.set_inst_name(\"foo_inst\");\n"
                       "    $display(\"name=%s\", c.option.name);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "name=foo_inst\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// §19.8 with §23.6: sample() and get_inst_coverage() reach the instance a
// hierarchical name denotes, u1's and not u2's.
TEST(CovergroupInstanceSim, MethodsReachInstanceThroughHierarchicalName) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module leaf;\n"
                 "  bit w;\n"
                 "  covergroup g; coverpoint w; endgroup\n"
                 "  g k = new;\n"
                 "endmodule\n"
                 "module top;\n"
                 "  leaf u1(); leaf u2();\n"
                 "  initial begin\n"
                 "    u1.k.sample();\n"
                 "    $display(\"%0.2f/%0.2f\", u1.k.get_inst_coverage(), "
                 "u2.k.get_inst_coverage());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "50.00/0.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// §19.8 with §23.6: sample() called through a hierarchical name reads the
// coverpoint expressions in the instance holding the covergroup, u1's v and
// the interface instance's v, never the caller's v of 3.
TEST(CovergroupInstanceSim, HierarchicalSampleReadsTheInstanceScope) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("interface ifc;\n"
                 "  bit [1:0] v;\n"
                 "  covergroup cg;\n"
                 "    coverpoint v { bins a = {0}; bins b = {1}; bins c = {2}; "
                 "bins d = {3}; }\n"
                 "  endgroup\n"
                 "  cg c = new;\n"
                 "endinterface\n"
                 "module leaf;\n"
                 "  bit [1:0] v;\n"
                 "  covergroup cg;\n"
                 "    coverpoint v { bins a = {0}; bins b = {1}; bins c = {2}; "
                 "bins d = {3}; }\n"
                 "  endgroup\n"
                 "  cg c = new;\n"
                 "endmodule\n"
                 "module top;\n"
                 "  bit [1:0] v = 3;\n"
                 "  leaf u1();\n"
                 "  ifc i();\n"
                 "  initial begin\n"
                 "    u1.v = 1; u1.c.sample(); u1.v = 2; u1.c.sample();\n"
                 "    i.v = 1; i.c.sample(); i.v = 2; i.c.sample();\n"
                 "    $display(\"%0.2f %0.2f\", u1.c.get_inst_coverage(),\n"
                 "             i.c.get_inst_coverage());\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "50.00 50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// §19.8 with §23.6 and §27.4: a covergroup instance held in a loop generate
// block instance or a named conditional generate block is reached from the
// enclosing module by the block's hierarchical name.
TEST(CovergroupInstanceSim, GenerateBlockInstanceReachedByHierarchicalName) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  bit [1:0] v;\n"
          "  covergroup cg;\n"
          "    coverpoint v { bins a = {0}; bins b = {1}; bins c = {2}; "
          "bins d = {3}; }\n"
          "  endgroup\n"
          "  for (genvar g = 0; g < 2; g++) begin : G\n"
          "    cg c = new;\n"
          "  end\n"
          "  if (1) begin : B\n"
          "    cg c = new;\n"
          "  end\n"
          "  initial begin\n"
          "    v = 1; G[1].c.sample(); B.c.sample(); v = 2; B.c.sample();\n"
          "    $display(\"%0.2f %0.2f %0.2f\", G[0].c.get_inst_coverage(),\n"
          "             G[1].c.get_inst_coverage(), "
          "B.c.get_inst_coverage());\n"
          "  end\n"
          "endmodule\n",
          f),
      "0.00 25.00 50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// §19.8 with §23.6 and §23.8: a name starting at the top-level module reaches
// the instance the bare name does, from the module itself and upward from an
// instance it holds.
TEST(CovergroupInstanceSim, TopRootedNameReachesInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture(
                "module leaf;\n"
                "  initial #1 top.c.sample();\n"
                "endmodule\n"
                "module top;\n"
                "  bit [1:0] v = 1;\n"
                "  covergroup cg; coverpoint v { bins a = {1}; bins b = {2}; } "
                "endgroup\n"
                "  cg c = new;\n"
                "  leaf u();\n"
                "  initial begin\n"
                "    #2 v = 2; top.c.sample();\n"
                "    $display(\"%0.2f\", c.get_inst_coverage());\n"
                "  end\n"
                "endmodule\n",
                f),
            "100.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// §19.8 with §25.9: an interface's covergroup instance is reached through a
// virtual interface, in a class method and in the module.
TEST(CovergroupInstanceSim, VirtualInterfaceReachesInstance) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "interface ifc;\n"
          "  bit [1:0] v;\n"
          "  covergroup cg; coverpoint v { bins a = {1}; bins b = {2}; } "
          "endgroup\n"
          "  cg c = new;\n"
          "endinterface\n"
          "class M;\n"
          "  virtual ifc vif;\n"
          "  function void hit(); vif.c.sample(); endfunction\n"
          "  function real r(); return vif.c.get_inst_coverage(); "
          "endfunction\n"
          "endclass\n"
          "module top;\n"
          "  ifc i();\n"
          "  M m;\n"
          "  virtual ifc w;\n"
          "  initial begin\n"
          "    m = new; m.vif = i; w = i;\n"
          "    i.v = 2; m.hit();\n"
          "    $display(\"%0.2f %0.2f\", m.r(), w.c.get_inst_coverage());\n"
          "  end\n"
          "endmodule\n",
          f),
      "50.00 50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// §19.8 with §8.6: a covergroup method called on the handle a function
// returns runs on the instance the handle refers to.
TEST(CovergroupInstanceSim, MethodOnReturnedHandleReachesTheInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture(
                "module top;\n"
                "  bit [1:0] v;\n"
                "  covergroup cg; coverpoint v { bins a = {1}; bins b = {2}; } "
                "endgroup\n"
                "  cg c = new;\n"
                "  function cg pick(); return c; endfunction\n"
                "  initial begin\n"
                "    v = 1; pick().sample();\n"
                "    $display(\"%0.2f %0.2f\", c.get_inst_coverage(),\n"
                "             pick().get_inst_coverage());\n"
                "  end\n"
                "endmodule\n",
                f),
            "50.00 50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// §19.8 with §8.6 and §11.3.1: sample() called as a statement on the handle a
// call returns evaluates that call once, as the expression form does.
TEST(CovergroupInstanceSim, SampleStatementOnReturnedHandleCallsItOnce) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  bit [1:0] v;\n"
                       "  int calls;\n"
                       "  covergroup cg; coverpoint v { bins a = {1}; bins b = "
                       "{2}; } endgroup\n"
                       "  cg c = new;\n"
                       "  function cg pick(); calls++; return c; endfunction\n"
                       "  initial begin\n"
                       "    v = 1; pick().sample();\n"
                       "    $display(\"%0d %0.2f\", calls, "
                       "c.get_inst_coverage());\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 50.00\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
}

// §19.8 (printed page 611): get_coverage() called on a coverpoint through the
// type, `cg::x::get_coverage(covered, total)`, counts that coverpoint's bins in
// every instance, the clause's own example giving 6 for x's 2 and 4 bins, of
// which cv1 has hit one. It answered cv1's whole covergroup, 2 of 5.
TEST(CoverageMethodSim, ACoverpointsTypeCoverageCountsItsBinsInEveryInstance) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int a, b, c, d, cov, tot;\n"
      "  string s;\n"
      "  covergroup cg (int xb, yb, ref int x, y);\n"
      "    coverpoint x {bins xbins[] = {[0:xb]};}\n"
      "    coverpoint y {bins ybins[] = {[0:yb]};}\n"
      "  endgroup\n"
      "  cg cv1 = new(1, 2, a, b);\n"
      "  cg cv2 = new(3, 6, c, d);\n"
      "  initial begin\n"
      "    a = 0; b = 0; c = 9; d = 9;\n"
      "    cv1.sample();\n"
      "    void'(cv1.x.get_inst_coverage(cov, tot)); s = "
      "$sformatf(\"%0d/%0d\", cov, tot);\n"
      "    void'(cv1.get_inst_coverage(cov, tot)); s = {s, $sformatf(\" "
      "%0d/%0d\", cov, tot)};\n"
      "    void'(cg::x::get_coverage(cov, tot)); s = {s, $sformatf(\" "
      "%0d/%0d\", cov, tot)};\n"
      "    void'(cg::get_coverage(cov, tot)); s = {s, $sformatf(\" %0d/%0d\", "
      "cov, tot)};\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1/2 2/5 1/6 2/16\n");
}

// §19.8, Table 19-5: stop() on a coverpoint or a cross stops collecting its
// coverage until start(), so the sample of 1 taken while cp is stopped counts
// nowhere and the cross keeps only its (0, 0) bin. Both kept counting.
TEST(CoverageMethodSim, StopOnACoverpointOrCrossStopsItsCollection) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  covergroup cg with function sample(int x, bit a, bit b);\n"
      "    cp: coverpoint x {bins b[] = {[0:3]};}\n"
      "    ca: coverpoint a;\n"
      "    cb: coverpoint b;\n"
      "    cr: cross ca, cb;\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  initial begin\n"
      "    c.sample(0, 0, 0);\n"
      "    c.cp.stop();\n"
      "    c.cr.stop();\n"
      "    c.sample(1, 1, 1);\n"
      "    $write(\"%0.2f \", c.cp.get_inst_coverage());\n"
      "    c.cp.start();\n"
      "    c.sample(2, 1, 1);\n"
      "    $display(\"%0.2f %0.2f\", c.cp.get_inst_coverage(), "
      "c.cr.get_inst_coverage());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "25.00 50.00 25.00\n");
}

// §19.8: stop() on a coverpoint of a real expression stops it as on an
// integral one, so c1's hi bin stays uncovered; and get_coverage() through an
// instance's coverpoint or cross, or through the type, `cg::ab::`, answers for
// that item over every instance: ca's instance coverages of 100 and 50
// average 75, ab's of 50 and 25 average 37.5, with 3 of the 8 cross bins of
// the two instances covered.
TEST(CoverageMethodSim, ARealCoverpointStopsAndCrossesReportTheirTypeCoverage) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  covergroup cg with function sample(real r, bit a, bit b);\n"
      "    cr: coverpoint r { bins lo = {[0.0:1.0]}; bins hi = {[2.0:3.0]}; }\n"
      "    ca: coverpoint a;\n"
      "    cb: coverpoint b;\n"
      "    ab: cross ca, cb;\n"
      "  endgroup\n"
      "  cg c1 = new, c2 = new;\n"
      "  int cov, tot;\n"
      "  initial begin\n"
      "    c1.sample(0.5, 0, 0);\n"
      "    c1.cr.stop();\n"
      "    c1.sample(2.5, 1, 1);\n"
      "    $write(\"%0.2f \", c1.cr.get_inst_coverage());\n"
      "    c2.sample(2.5, 0, 1);\n"
      "    $write(\"%0.2f %0.2f \", c1.ca.get_coverage(), "
      "c1.ab.get_coverage());\n"
      "    void'(cg::ab::get_coverage(cov, tot));\n"
      "    $display(\"%0d/%0d\", cov, tot);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "50.00 75.00 37.50 3/8\n");
}

}  // namespace
