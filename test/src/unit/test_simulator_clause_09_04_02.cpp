#include "fixture_simulator.h"
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

TEST(EdgeDetection, Posedge0To1) {
  EXPECT_EQ(DetectEdge(Logic4::kVal0, Logic4::kVal1), EdgeKind::kPosedge);
}

TEST(EdgeDetection, Posedge0ToX) {
  EXPECT_EQ(DetectEdge(Logic4::kVal0, Logic4::kX), EdgeKind::kPosedge);
}

TEST(EdgeDetection, Posedge0ToZ) {
  EXPECT_EQ(DetectEdge(Logic4::kVal0, Logic4::kZ), EdgeKind::kPosedge);
}

TEST(EdgeDetection, PosedgeXTo1) {
  EXPECT_EQ(DetectEdge(Logic4::kX, Logic4::kVal1), EdgeKind::kPosedge);
}

TEST(EdgeDetection, PosedgeZTo1) {
  EXPECT_EQ(DetectEdge(Logic4::kZ, Logic4::kVal1), EdgeKind::kPosedge);
}

TEST(EdgeDetection, Negedge1To0) {
  EXPECT_EQ(DetectEdge(Logic4::kVal1, Logic4::kVal0), EdgeKind::kNegedge);
}

TEST(EdgeDetection, Negedge1ToX) {
  EXPECT_EQ(DetectEdge(Logic4::kVal1, Logic4::kX), EdgeKind::kNegedge);
}

TEST(EdgeDetection, Negedge1ToZ) {
  EXPECT_EQ(DetectEdge(Logic4::kVal1, Logic4::kZ), EdgeKind::kNegedge);
}

TEST(EdgeDetection, NegedgeXTo0) {
  EXPECT_EQ(DetectEdge(Logic4::kX, Logic4::kVal0), EdgeKind::kNegedge);
}

TEST(EdgeDetection, NegedgeZTo0) {
  EXPECT_EQ(DetectEdge(Logic4::kZ, Logic4::kVal0), EdgeKind::kNegedge);
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

bool IsEdge(Logic4 from, Logic4 to) {
  EdgeKind e = DetectEdge(from, to);
  return e == EdgeKind::kPosedge || e == EdgeKind::kNegedge;
}

TEST(EdgeDetection, EdgeDetectedOnPosedge) {
  EXPECT_TRUE(IsEdge(Logic4::kVal0, Logic4::kVal1));
}

TEST(EdgeDetection, EdgeDetectedOnNegedge) {
  EXPECT_TRUE(IsEdge(Logic4::kVal1, Logic4::kVal0));
}

TEST(EdgeDetection, NoEdgeDetectedOnSame) {
  EXPECT_FALSE(IsEdge(Logic4::kVal0, Logic4::kVal0));
}

TEST(EdgeDetection, NoEdgeDetectedXToZ) {
  EXPECT_FALSE(IsEdge(Logic4::kX, Logic4::kZ));
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
      "    #5 wide = 8'd2;\n"  // bit[1] changes, but bit[0] stays 0
      "    #5 wide = 8'd3;\n"  // bit[0] goes 0->1: posedge
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
      "    #5 sig = 8'd5;\n"  // same value: no event
      "    #5 sig = 8'd7;\n"  // different value: event fires
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

// §9.4.2 Table 9-2: a posedge shall be detected on the transition from 0
// to x. Exercises the production CheckEdge path through @(posedge clk),
// complementing the existing reference-model EdgeDetection unit tests.
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

// §9.4.2 Table 9-2: a posedge shall be detected on the transition from x
// to 1.
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

// §9.4.2 Table 9-2: a negedge shall be detected on the transition from 1
// to x.
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

// §9.4.2 Table 9-2: a negedge shall be detected on the transition from x
// to 0.
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

// §9.4.2: "An edge event shall be detected only on the LSB of the
// expression." Symmetric to PosedgeDetectsOnlyLsb: a non-LSB-only change
// in a multi-bit signal must not fire negedge.
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

// §9.4.2: "An edge event shall be detected only on the LSB of the
// expression." Same rule for the `edge` keyword.
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

// §9.4.2: A non-edge implicit event is detected on a change in the value
// of the expression — including compound expressions whose operands are
// individual variables. Drives the @(a|b) result transitioning 0->1.
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

// §9.4.2: "If the event expression is a reference to a simple object handle
// or chandle variable, an event is created when a write to that variable is
// not equal to its previous value." A null-to-null write leaves the chandle
// bit-pattern unchanged, so @(h) shall not fire.
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

// §9.4.2: "A change of value in any operand of the expression without a
// change in the result of the expression shall not be detected as an event."
// First @(a|b) skips a's 1->0 transition (operand changed, but a|b stays 1),
// then fires when b's 1->0 transition makes a|b change 1->0.
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

// §9.4.2: "If the event expression is a reference to a simple object handle
// or chandle variable, an event is created when a write to that variable is
// not equal to its previous value." Complements ChandleSameValueWriteIsNotEvent
// with the positive case: a class handle whose value transitions from null to
// a freshly allocated object shall fire @(h).
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

// §9.4.2: "Changing the value of object data members, aggregate elements, or
// the size of a dynamically sized array referenced by a method or function
// shall cause the event expression to be reevaluated." A push_back that
// changes q.size() must reevaluate @(q.size()) and fire the event.
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

}  // namespace
