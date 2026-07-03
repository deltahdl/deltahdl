#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ProceduralContinuousAssignSim, AssignRhsReevaluatesOnVariableChange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, q;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "    assign q = a + b;\n"
      "    #1;\n"
      "    a = 8'd100;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 120u);
}

TEST(ProceduralContinuousAssignSim, ForceRhsReevaluatesOnVariableChange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] b, c, a;\n"
      "  initial begin\n"
      "    b = 8'd1;\n"
      "    c = 8'd2;\n"
      "    force a = b + c;\n"
      "    #1;\n"
      "    b = 8'd50;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 52u);
}

// The head's rule treats the assign/force RHS as a continuous assignment,
// reevaluating it whenever *any* RHS variable changes. The LRM's own example
// is `force a = b + f(c)`, where a variable (c) appears only as a function-call
// argument -- it must still be a reevaluation source.
TEST(ProceduralContinuousAssignSim,
     ForceReevaluatesOnFunctionCallArgumentChange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] b, c, a;\n"
      "  function logic [7:0] dbl(input logic [7:0] x);\n"
      "    return x + x;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    b = 8'd1;\n"
      "    c = 8'd2;\n"
      "    force a = b + dbl(c);\n"
      "    #1;\n"
      "    c = 8'd10;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  // b + dbl(c) = 1 + (10+10) = 21; unchanged (5) if the func-call argument
  // were not collected as a reevaluation source.
  EXPECT_EQ(a->value.ToUint64(), 21u);
}

TEST(ProceduralContinuousAssignSim, ForceReevaluatesForEachRhsVariableChange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] b, c, a;\n"
      "  initial begin\n"
      "    b = 8'd1;\n"
      "    c = 8'd2;\n"
      "    force a = b + c;\n"
      "    #1; b = 8'd10;\n"
      "    #1; c = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 30u);
}

}  // namespace
