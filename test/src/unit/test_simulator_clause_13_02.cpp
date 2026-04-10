#include "helpers_scheduler.h"

namespace {

TEST(SubroutineOverviewSim, NonvoidFunctionAsOperandInExpr) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  function logic [31:0] five; return 32'd5; endfunction\n"
      "  initial x = five() + 32'd3;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(val, 8u);
}

}  // namespace
