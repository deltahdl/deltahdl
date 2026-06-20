#include "fixture_simulator.h"
#include "helpers_stmt_exec.h"
#include "simulator/awaiters.h"
#include "simulator/clocking.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(EventControlSim, EventControlPosedge) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    @(posedge clk) x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(EventControlSim, EventControlNegedge) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1;\n"
      "    #5 clk = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    @(negedge clk) x = 8'd77;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(EventControlSim, EventControlAnyChange) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sig;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    sig = 8'd0;\n"
      "    #5 sig = 8'd5;\n"
      "  end\n"
      "  initial begin\n"
      "    @(sig) x = 8'd33;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

TEST(EventControlSim, SequentialPosedgeThenNegedge) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic clk;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    #5 clk = 1;\n"
      "    #5 clk = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    @(posedge clk) a = 8'd1;\n"
      "    @(negedge clk) b = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 2u);
}

enum class Logic4 : uint8_t {
  kVal0 = 0,
  kVal1 = 1,
  kX = 2,
  kZ = 3,
};

enum class EdgeKind : uint8_t {
  kNone,
  kPosedge,
  kNegedge,
};

EdgeKind DetectEdge(Logic4 from, Logic4 to) {
  if (from == to) return EdgeKind::kNone;
  if (from == Logic4::kVal0 &&
      (to == Logic4::kVal1 || to == Logic4::kX || to == Logic4::kZ))
    return EdgeKind::kPosedge;
  if ((from == Logic4::kX || from == Logic4::kZ) && to == Logic4::kVal1)
    return EdgeKind::kPosedge;
  if (from == Logic4::kVal1 &&
      (to == Logic4::kVal0 || to == Logic4::kX || to == Logic4::kZ))
    return EdgeKind::kNegedge;
  if ((from == Logic4::kX || from == Logic4::kZ) && to == Logic4::kVal0)
    return EdgeKind::kNegedge;
  return EdgeKind::kNone;
}

TEST(EdgeDetection, NoEdge0To0) {
  EXPECT_EQ(DetectEdge(Logic4::kVal0, Logic4::kVal0), EdgeKind::kNone);
}

TEST(EdgeDetection, NoEdge1To1) {
  EXPECT_EQ(DetectEdge(Logic4::kVal1, Logic4::kVal1), EdgeKind::kNone);
}

TEST(EdgeDetection, NoEdgeXToX) {
  EXPECT_EQ(DetectEdge(Logic4::kX, Logic4::kX), EdgeKind::kNone);
}

TEST(EdgeDetection, NoEdgeXToZ) {
  EXPECT_EQ(DetectEdge(Logic4::kX, Logic4::kZ), EdgeKind::kNone);
}

TEST(EdgeDetection, NoEdgeZToX) {
  EXPECT_EQ(DetectEdge(Logic4::kZ, Logic4::kX), EdgeKind::kNone);
}

TEST(EdgeDetection, NoEdgeZToZ) {
  EXPECT_EQ(DetectEdge(Logic4::kZ, Logic4::kZ), EdgeKind::kNone);
}

TEST(EventControlSim, EdgeEventFiresOnPosedge) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sig;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    sig = 0;\n"
      "    #5 sig = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    @(edge sig) x = 8'd10;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(EventControlSim, EdgeEventFiresOnNegedge) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sig;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    sig = 1;\n"
      "    #5 sig = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    @(edge sig) x = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

TEST(EventControlSim, PosedgeDetectsOnlyLsb) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] wide;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    wide = 8'd0;\n"
      "    #5 wide = 8'd2;\n"
      "    #5 wide = 8'd3;\n"
      "  end\n"
      "  initial begin\n"
      "    @(posedge wide) x = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(EventControlSim, NoEventOnSameValueWrite) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sig;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    sig = 8'd5;\n"
      "    #5 sig = 8'd5;\n"
      "    #5 sig = 8'd7;\n"
      "  end\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    @(sig) x = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(EventControlSim, PosedgeFiresOnZeroToZ) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    #5 clk = 1'bz;\n"
      "  end\n"
      "  initial begin\n"
      "    @(posedge clk) x = 8'd55;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

TEST(EventControlSim, PosedgeFiresOnZToOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1'bz;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    @(posedge clk) x = 8'd66;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 66u);
}

TEST(EventControlSim, NegedgeFiresOnOneToZ) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1;\n"
      "    #5 clk = 1'bz;\n"
      "  end\n"
      "  initial begin\n"
      "    @(negedge clk) x = 8'd77;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(EventControlSim, NegedgeFiresOnZToZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1'bz;\n"
      "    #5 clk = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    @(negedge clk) x = 8'd88;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

TEST(EventControlSim, PosedgeFiresOnZeroToX) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 0;\n"
      "    #5 clk = 1'bx;\n"
      "  end\n"
      "  initial begin\n"
      "    @(posedge clk) x = 8'd11;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 11u);
}

TEST(EventControlSim, PosedgeFiresOnXToOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1'bx;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    @(posedge clk) x = 8'd22;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 22u);
}

TEST(EventControlSim, NegedgeFiresOnOneToX) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1;\n"
      "    #5 clk = 1'bx;\n"
      "  end\n"
      "  initial begin\n"
      "    @(negedge clk) x = 8'd33;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

TEST(EventControlSim, NegedgeFiresOnXToZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1'bx;\n"
      "    #5 clk = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    @(negedge clk) x = 8'd44;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 44u);
}

TEST(EventControlSim, NegedgeDetectsOnlyLsb) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] wide;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    wide = 8'd3;\n"
      "    #5 wide = 8'd1;\n"
      "    #5 wide = 8'd0;\n"
      "  end\n"
      "  initial begin\n"
      "    @(negedge wide) x = 8'd55;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

TEST(EventControlSim, EdgeDetectsOnlyLsb) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] wide;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    wide = 8'd0;\n"
      "    #5 wide = 8'd2;\n"
      "    #5 wide = 8'd3;\n"
      "  end\n"
      "  initial begin\n"
      "    @(edge wide) x = 8'd66;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 66u);
}

TEST(EventControlSim, NoPosedgeOnXToZ) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1'bx;\n"
      "    #5 clk = 1'bz;\n"
      "  end\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    @(posedge clk) x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(EventControlSim, NoPosedgeOnZToX) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1'bz;\n"
      "    #5 clk = 1'bx;\n"
      "  end\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    @(posedge clk) x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(EventControlSim, NoNegedgeOnXToZ) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1'bx;\n"
      "    #5 clk = 1'bz;\n"
      "  end\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    @(negedge clk) x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(EventControlSim, NoNegedgeOnZToX) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1'bz;\n"
      "    #5 clk = 1'bx;\n"
      "  end\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    @(negedge clk) x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(EventControlSim, CompoundExprResultChangeFiresEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    a = 0; b = 0;\n"
      "    x = 8'd0;\n"
      "    #5 a = 1;\n"
      "    #5 $finish;\n"
      "  end\n"
      "  initial @(a | b) x = 8'd99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(EventControlSim, ChandleSameValueWriteIsNotEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  chandle h;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    #5 h = null;\n"
      "    #5 $finish;\n"
      "  end\n"
      "  initial @(h) x = 8'd99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(EventControlSim, CompoundExprOperandChangeWithoutResultChangeIsNotEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a, b;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    a = 1; b = 1;\n"
      "    x = 8'd0;\n"
      "    #5 a = 0;\n"
      "    #5 b = 0;\n"
      "    #5 $finish;\n"
      "  end\n"
      "  initial begin\n"
      "    @(a | b) x = 8'd99;\n"
      "    @(a | b) x = 8'd55;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(EventControlSim, ObjectHandleChangeFiresEvent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  class C;\n"
      "  endclass\n"
      "  C h;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    h = null;\n"
      "    #5 h = new();\n"
      "    #5 $finish;\n"
      "  end\n"
      "  initial @(h) x = 8'd77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(EventControlSim, DynamicArraySizeChangeReevaluatesEventExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int q[$];\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    #5 q.push_back(42);\n"
      "    #5 $finish;\n"
      "  end\n"
      "  initial @(q.size()) x = 8'd88;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

TEST(EventControlSim, NoEdgeOnXToZ) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1'bx;\n"
      "    #5 clk = 1'bz;\n"
      "  end\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    @(edge clk) x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(EventControlSim, NoEdgeOnZToX) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1'bz;\n"
      "    #5 clk = 1'bx;\n"
      "  end\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    @(edge clk) x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(EventControlSim, EdgeFiresOnXToOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1'bx;\n"
      "    #5 clk = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    @(edge clk) x = 8'd33;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

TEST(EventControlSim, EdgeFiresOnZToZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    clk = 1'bz;\n"
      "    #5 clk = 0;\n"
      "  end\n"
      "  initial begin\n"
      "    @(edge clk) x = 8'd44;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 44u);
}

TEST(EventControlSim, ClockingBlockInputResolvesThroughClockingManager) {
  SimFixture f;

  auto* data = f.ctx.CreateVariable("data", 8);
  data->value = MakeLogic4VecVal(f.arena, 8, 0x00);

  ClockingManager cmgr;
  ClockingBlock block;
  block.name = "cb";
  block.clock_signal = "clk";
  block.clock_edge = Edge::kPosedge;
  ClockingSignal sig;
  sig.signal_name = "data";
  sig.direction = ClockingDir::kInput;
  block.signals.push_back(sig);
  cmgr.Register(block);
  f.ctx.SetClockingManager(&cmgr);

  auto* member = f.arena.Create<Expr>();
  member->kind = ExprKind::kMemberAccess;
  member->lhs = f.arena.Create<Expr>();
  member->lhs->kind = ExprKind::kIdentifier;
  member->lhs->text = "cb";
  member->rhs = f.arena.Create<Expr>();
  member->rhs->kind = ExprKind::kIdentifier;
  member->rhs->text = "data";

  auto* wait_stmt = f.arena.Create<Stmt>();
  wait_stmt->kind = StmtKind::kEventControl;
  EventExpr ev;
  ev.edge = Edge::kNone;
  ev.signal = member;
  wait_stmt->events.push_back(ev);
  auto* null_body = f.arena.Create<Stmt>();
  null_body->kind = StmtKind::kNull;
  wait_stmt->body = null_body;

  EXPECT_EQ(data->watchers.size(), 0u);

  DriverResult result;
  auto coro = DriverCoroutine(wait_stmt, f.ctx, f.arena, &result);
  coro.Resume();

  EXPECT_EQ(data->watchers.size(), 1u);
}

TEST(EventControlSim, NamedEventTriggerReleasesWaiter) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  event e;\n"
      "  int hit;\n"
      "  initial begin\n"
      "    hit = 0;\n"
      "    fork\n"
      "      begin @e; hit = 1; end\n"
      "      begin #1 ->e; end\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("hit");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

}  // namespace
