#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/coverage.h"

using namespace delta;

namespace {

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

// §19.3: a covergroup with a clocking event samples at each occurrence of the
// event. a is 1 at the posedges at 5 and 45 and 0 at 15, 25 and 35, and a_d1
// follows it a cycle later, so every bin of both coverpoints is hit.
TEST(CovergroupInstanceSim, ClockingEventSamplesEachEdge) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "module top;\n"
          "  logic clk = 0, a = 1;\n"
          "  bit a_d1 = 0;\n"
          "  always #5 clk = ~clk;\n"
          "  always_ff @(posedge clk) a_d1 <= a;\n"
          "  covergroup cg @(posedge clk);\n"
          "    cp: coverpoint a { bins lo = {1'b0}; bins hi = {1'b1}; }\n"
          "    cpd: coverpoint a_d1 { bins lo = {1'b0}; bins hi = {1'b1}; }\n"
          "    option.per_instance = 1;\n"
          "  endgroup\n"
          "  cg cg_1 = new();\n"
          "  initial begin\n"
          "    #12 a = 0; #20 a = 1; #20;\n"
          "    $display(\"cov=%0d\", $rtoi(cg_1.get_inst_coverage()));\n"
          "    $finish;\n"
          "  end\n"
          "endmodule\n",
          f),
      "cov=100\n$finish at time 52\n");
}

}  // namespace
