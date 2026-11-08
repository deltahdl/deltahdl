#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockSimulation, SamePrecisionRoundsFractionalDelayUp) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  integer x;\n"
                      "  initial begin\n"
                      "    #2.75 x = $time;\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            3u);
}

TEST(DesignBuildingBlockSimulation, SamePrecisionRoundsFractionalDelayDown) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  integer x;\n"
                      "  initial begin\n"
                      "    #2.3 x = $time;\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            2u);
}

TEST(DesignBuildingBlockSimulation, SamePrecisionRoundsHalfAwayFromZero) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  integer x;\n"
                      "  initial begin\n"
                      "    #2.5 x = $time;\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            3u);
}

TEST(DesignBuildingBlockSimulation, OneOrderSmallerKeepsOneDecimal) {
  EXPECT_DOUBLE_EQ(RunAndGetReal("module t;\n"
                                 "  timeunit 1ns / 100ps;\n"
                                 "  real x;\n"
                                 "  initial begin\n"
                                 "    #2.75 x = $realtime;\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "x"),
                   2.8);
}

TEST(DesignBuildingBlockSimulation, OneOrderSmallerRoundsDown) {
  EXPECT_DOUBLE_EQ(RunAndGetReal("module t;\n"
                                 "  timeunit 1ns / 100ps;\n"
                                 "  real x;\n"
                                 "  initial begin\n"
                                 "    #2.73 x = $realtime;\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "x"),
                   2.7);
}

TEST(DesignBuildingBlockSimulation, DelayHeldToOwnElementPrecision) {
  EXPECT_DOUBLE_EQ(RunAndGetReal("module sub;\n"
                                 "  timeunit 1ns / 1ps;\n"
                                 "endmodule\n"
                                 "module t;\n"
                                 "  timeunit 1ns / 100ps;\n"
                                 "  sub s();\n"
                                 "  real x;\n"
                                 "  initial begin\n"
                                 "    #2.756 x = $realtime;\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "x"),
                   2.8);
}

TEST(DesignBuildingBlockSimulation, DelayHeldToACoarserUnitOfPrecision) {
  EXPECT_DOUBLE_EQ(RunAndGetReal("module sub;\n"
                                 "  timeunit 1ns / 1ps;\n"
                                 "endmodule\n"
                                 "module t;\n"
                                 "  timeunit 1ns / 1ns;\n"
                                 "  sub s();\n"
                                 "  real x;\n"
                                 "  initial begin\n"
                                 "    #1.3 x = $realtime;\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "x"),
                   1.0);
}

TEST(DesignBuildingBlockSimulation, IntraAssignmentDelayRounds) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  integer x;\n"
                      "  initial begin\n"
                      "    x = #2.75 1;\n"
                      "    x = $time;\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            3u);
}

TEST(DesignBuildingBlockSimulation, IntegerDelayIsUnchanged) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  integer x;\n"
                      "  initial begin\n"
                      "    #5 x = $time;\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            5u);
}

TEST(DesignBuildingBlockSimulation, VariableSourcedFractionalDelayRounds) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  integer x;\n"
                      "  real d;\n"
                      "  initial begin\n"
                      "    d = 2.75;\n"
                      "    #d x = $time;\n"
                      "  end\n"
                      "endmodule\n",
                      "x"),
            3u);
}

TEST(DesignBuildingBlockSimulation, TwoOrdersSmallerKeepsTwoDecimals) {
  EXPECT_DOUBLE_EQ(RunAndGetReal("module t;\n"
                                 "  timeunit 1ns / 10ps;\n"
                                 "  real x;\n"
                                 "  initial begin\n"
                                 "    #2.756 x = $realtime;\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "x"),
                   2.76);
}

TEST(DesignBuildingBlockSimulation, ExactPrecisionMultipleUnchanged) {
  EXPECT_DOUBLE_EQ(RunAndGetReal("module t;\n"
                                 "  timeunit 1ns / 100ps;\n"
                                 "  real x;\n"
                                 "  initial begin\n"
                                 "    #2.8 x = $realtime;\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "x"),
                   2.8);
}

}  // namespace
