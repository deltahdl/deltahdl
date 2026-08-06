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

}  // namespace
