#include <gtest/gtest.h>

#include <iostream>
#include <sstream>
#include <streambuf>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §17.6 with §16.11: a checker triggers its covergroup from a sequence match
// item, `cg_1.sample()` beside the sequence's condition, and the call does not
// alter the match. v1 is high at the posedges at 5 and 15 and v2 throughout,
// so `v1 ##1 v2` matches at 15 and 25 and the cover property succeeds twice.
// The call was not read as a match item, and the cover never succeeded.
TEST(CheckerCovergroup, SampledFromASequenceMatchItem) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      "checker chk(logic clk, v1, v2, logic [3:0] op);\n"
      "  bit [3:0] op_d1;\n"
      "  int hits = 0;\n"
      "  always_ff @(posedge clk) op_d1 <= op;\n"
      "  covergroup cg;\n"
      "    cp: coverpoint op_d1 { bins three = {4'd3}; }\n"
      "  endgroup\n"
      "  cg cg_1 = new();\n"
      "  sequence s;\n"
      "    @(posedge clk) v1 ##1 (v2, cg_1.sample());\n"
      "  endsequence\n"
      "  c1: cover property (s) hits++;\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0, v1 = 0, v2 = 1;\n"
      "  logic [3:0] op = 4'd3;\n"
      "  always #5 clk = ~clk;\n"
      "  chk c(clk, v1, v2, op);\n"
      "  initial begin #2 v1 = 1; #20 v1 = 0; #30 $finish; end\n"
      "endmodule\n",
      f, "c.hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
}

// §17.6 with §19.3: a covergroup declared in a checker is instantiated per
// checker instance and sampled there, by an explicit sample() from an
// always_ff and by its own clocking event alike.
TEST(CheckerCovergroup, InstanceSampledExplicitlyAndByItsEvent) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture(
          "checker chk(logic a, logic clk);\n"
          "  covergroup cg;\n"
          "    cp: coverpoint a { bins lo = {1'b0}; bins hi = {1'b1}; }\n"
          "  endgroup\n"
          "  covergroup cge @(posedge clk);\n"
          "    cp: coverpoint a { bins lo = {1'b0}; bins hi = {1'b1}; }\n"
          "  endgroup\n"
          "  cg cg_1 = new();\n"
          "  cge cg_2 = new();\n"
          "  always_ff @(posedge clk) cg_1.sample();\n"
          "  final $display(\"cov=%0d %0d\", $rtoi(cg_1.get_inst_coverage()),\n"
          "                 $rtoi(cg_2.get_inst_coverage()));\n"
          "endchecker\n"
          "module top;\n"
          "  logic clk = 0, a = 1;\n"
          "  always #5 clk = ~clk;\n"
          "  chk c(a, clk);\n"
          "  initial begin #12 a = 0; #20 a = 1; #20 $finish; end\n"
          "endmodule\n",
          f),
      "$finish at time 52\n");
  // The final procedure reports, run as the end of simulation runs it.
  std::ostringstream reported;
  std::streambuf* old_buf = std::cout.rdbuf(reported.rdbuf());
  f.ctx.RunFinalBlocks();
  std::cout.rdbuf(old_buf);
  EXPECT_EQ(reported.str(), "cov=100 100\n");
}

}  // namespace
