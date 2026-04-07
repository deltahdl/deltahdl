#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LoopSyntaxSimulation, ForCompoundAssignStep) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] total;\n"
      "  initial begin\n"
      "    total = 8'd0;\n"
      "    for (int i = 0; i < 10; i += 2)\n"
      "      total = total + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("total");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(LoopSyntaxSimulation, ForPreDecrementStep) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] last;\n"
      "  initial begin\n"
      "    last = 8'd0;\n"
      "    for (int i = 5; i > 0; --i)\n"
      "      last = i[7:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("last");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(LoopSyntaxSimulation, ForPreIncrementStep) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] total;\n"
      "  initial begin\n"
      "    total = 8'd0;\n"
      "    for (int i = 0; i < 5; ++i)\n"
      "      total = total + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("total");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

}  // namespace
