#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LoopStatementSim, ContinueJumpsToEndOfWhileBody) {
  SimFixture f;
  auto* count = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x, count;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    count = 8'd0;\n"
      "    while (x < 8'd6) begin\n"
      "      x = x + 8'd1;\n"
      "      if (x == 8'd3) continue;\n"
      "      count = count + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f, "count");
  ASSERT_NE(count, nullptr);

  EXPECT_EQ(count->value.ToUint64(), 5u);
}

}  // namespace
