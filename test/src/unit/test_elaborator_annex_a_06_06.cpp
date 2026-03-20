#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(PatternElaboration, MatchesInIfElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    x = 8'd3;\n"
      "    if (x matches 8'd3) y = 8'd1;\n"
      "    else y = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

TEST(ConditionalElaboration, IfElseInAlwaysComb) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  logic a, x;\n"
      "  always_comb begin\n"
      "    if (a) x = 1;\n"
      "    else x = 0;\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ConditionalElaboration, UniqueIfInAlwaysComb) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] x;\n"
      "  always_comb begin\n"
      "    unique if (sel == 2'd0) x = 8'd0;\n"
      "    else if (sel == 2'd1) x = 8'd1;\n"
      "    else x = 8'd2;\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ConditionalElaboration, IfWithTripleAndElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  logic a, b, x;\n"
      "  initial begin\n"
      "    if (a &&& b) x = 1;\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ConditionalElaboration, NestedIfInFunction) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  function int pick(input int a, input int b, input int sel);\n"
      "    if (sel) return a;\n"
      "    else return b;\n"
      "  endfunction\n"
      "endmodule\n"));
}

TEST(ConditionalElaboration, IfElseIfElseInAlwaysLatch) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  logic a, b, x;\n"
      "  always_latch begin\n"
      "    if (a) x = 1;\n"
      "    else if (b) x = 0;\n"
      "  end\n"
      "endmodule\n"));
}

}  // namespace
