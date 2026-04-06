#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ConditionalElaboration, BasicIfElseElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x, y;\n"
      "  initial begin\n"
      "    x = 10;\n"
      "    if (x == 10)\n"
      "      y = 1;\n"
      "    else\n"
      "      y = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

TEST(ConditionalElaboration,MatchesInIfElaborates) {
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

TEST(ConditionalElaboration, IfWithoutElseElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  logic a, x;\n"
      "  initial begin\n"
      "    if (a) x = 1;\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ConditionalElaboration, BothBranchesNullElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    if (a) ;\n"
      "    else ;\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ConditionalElaboration, NestedIfElseInInitial) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  logic a, b, x;\n"
      "  initial begin\n"
      "    if (a) begin\n"
      "      if (b) x = 1;\n"
      "      else x = 0;\n"
      "    end else begin\n"
      "      x = 0;\n"
      "    end\n"
      "  end\n"
      "endmodule\n"));
}

}  // namespace
