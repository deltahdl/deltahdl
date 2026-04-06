#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(IfElseIfElaboration, AlwaysCombPriorityEncoder) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial a = 8'd15;\n"
      "  always_comb begin\n"
      "    if (a > 8'd20)\n"
      "      result = 8'd3;\n"
      "    else if (a > 8'd10)\n"
      "      result = 8'd2;\n"
      "    else if (a > 8'd5)\n"
      "      result = 8'd1;\n"
      "    else\n"
      "      result = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 2u);
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

TEST(IfElseIfElaboration, IfElseIfNoFinalElseElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  logic a, b, x;\n"
      "  initial begin\n"
      "    if (a) x = 1;\n"
      "    else if (b) x = 0;\n"
      "  end\n"
      "endmodule\n"));
}

TEST(IfElseIfElaboration, IfElseIfInInitialElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, x;\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    if (a == 8'd0) x = 8'd10;\n"
      "    else if (a == 8'd1) x = 8'd20;\n"
      "    else x = 8'd30;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

}  // namespace
