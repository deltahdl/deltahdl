#include "fixture_simulator.h"

using namespace delta;

namespace {

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
