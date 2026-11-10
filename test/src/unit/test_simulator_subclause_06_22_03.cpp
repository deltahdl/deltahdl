#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(AssignmentCompatibleSimulation, NarrowerSinkTruncatesUpperBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  logic [15:0] wide;\n"
      "  logic [7:0]  narrow;\n"
      "  initial begin\n"
      "    wide = 16'hABCD;\n"
      "    narrow = wide;\n"
      "  end\n"
      "endmodule\n",
      f, "narrow");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

TEST(AssignmentCompatibleSimulation, EquivalentAssignmentPropagatesValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module top;\n"
      "  reg   [7:0] r;\n"
      "  logic [7:0] l;\n"
      "  initial begin\n"
      "    r = 8'h77;\n"
      "    l = r;\n"
      "  end\n"
      "endmodule\n",
      f, "l");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x77u);
}

TEST(AssignmentCompatibleSimulation, ConversionsRoundRealsAndTruncateIntegers) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int i, j; byte y; real r;\n"
                       "  initial begin\n"
                       "    i = 2.5; j = -2.5; y = 300; r = 3;\n"
                       "    $display(\"%0d %0d %0d %0.1f\", i, j, y, r);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "3 -3 44 3.0\n");
}

}  // namespace
