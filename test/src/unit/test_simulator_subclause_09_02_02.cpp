#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(AlwaysRepeatsSim, GeneralPurposeAlwaysWithDelayLoops) {
  SimFixture f;
  auto* count = RunAndFindVar(
      "module t;\n"
      "  integer count;\n"
      "  initial begin\n"
      "    count = 0;\n"
      "    #55 $finish;\n"
      "  end\n"
      "  always #10 count = count + 1;\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(count, nullptr);
  EXPECT_EQ(count->value.ToUint64(), 5u);
}

TEST(AlwaysRepeatsSim, GeneralPurposeAlwaysWithEventControlLoops) {
  SimFixture f;
  auto* n = RunAndFindVar(
      "module t;\n"
      "  reg clk;\n"
      "  integer n;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    n = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "    #5 clk = 1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "  always @(posedge clk) n = n + 1;\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 2u);
}

TEST(AlwaysRepeatsSim, AlwaysCombReevaluatesOnEachChange) {
  SimFixture f;
  auto* y = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, y;\n"
      "  initial begin\n"
      "    a = 8'd1;\n"
      "    #5 a = 8'd5;\n"
      "    #5 a = 8'd9;\n"
      "    #5 $finish;\n"
      "  end\n"
      "  always_comb y = a + 8'd1;\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 10u);
}

TEST(AlwaysRepeatsSim, AlwaysLatchReevaluatesWhileEnabled) {
  SimFixture f;
  auto* q = RunAndFindVar(
      "module t;\n"
      "  logic en;\n"
      "  logic [7:0] d, q;\n"
      "  initial begin\n"
      "    en = 1'b0;\n"
      "    d = 8'd0;\n"
      "    #5 en = 1'b1;\n"
      "    d = 8'd3;\n"
      "    #5 d = 8'd7;\n"
      "    #5 $finish;\n"
      "  end\n"
      "  always_latch if (en) q = d;\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 7u);
}

TEST(AlwaysRepeatsSim, AlwaysFfFiresOnEachClockEdge) {
  SimFixture f;
  auto* count = RunAndFindVar(
      "module t;\n"
      "  reg clk;\n"
      "  integer count = 0;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "    #5 clk = 1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "  always_ff @(posedge clk) count <= count + 1;\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(count, nullptr);
  EXPECT_EQ(count->value.ToUint64(), 3u);
}

}  // namespace
