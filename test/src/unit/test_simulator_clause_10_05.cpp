#include "fixture_simulator.h"
#include "helpers_lower_run.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(VariableInitSim, VarInitBeforeInitialBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x = 42;\n"
      "  int y;\n"
      "  initial y = x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);

  EXPECT_EQ(y->value.ToUint64(), 42u);
}

TEST(VariableInitSim, VarInitIsNotContinuous) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a = 8'd10;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    b = a;\n"
      "    a = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);

  EXPECT_EQ(a->value.ToUint64(), 99u);

  EXPECT_EQ(b->value.ToUint64(), 10u);
}

TEST(VariableInitSim, VarInitHoldsUntilAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x = 100;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);

  EXPECT_EQ(x->value.ToUint64(), 100u);
}

TEST(VariableInitSim, VarInitWithExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] v = 8'hF0 & 8'h3C;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 0x30u);
}

TEST(VariableInitSim, MultipleVarInitSameDecl) {
  SimFixture f;
  auto* design = ElaborateLowerRun(f,
                                   "module t;\n"
                                   "  int a = 1, b = 2, c = 3;\n"
                                   "endmodule\n");
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("c")->value.ToUint64(), 3u);
}

TEST(VariableInitSim, VarInitBeforeAlwaysBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk = 0;\n"
      "  logic [7:0] count = 8'd5;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    #1 clk = 1;\n"
      "  end\n"
      "  always_ff @(posedge clk) begin\n"
      "    result <= count;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* result = f.ctx.FindVariable("result");
  ASSERT_NE(result, nullptr);

  EXPECT_EQ(result->value.ToUint64(), 5u);
}

TEST(VariableInitSim, VarInitOverwrittenByProceduralAssign) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x = 100;\n"
      "  initial x = 200;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 200u);
}

TEST(VariableInitSim, BlockLevelVarInit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    int local_var = 77;\n"
      "    result = local_var;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* result = f.ctx.FindVariable("result");
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result->value.ToUint64(), 77u);
}

TEST(VariableInitSim, StaticClassMemberInitBeforeInitialBlock) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  static int val = 55;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial result = C::val;\n"
                      "endmodule\n",
                      "result"),
            55u);
}

// The initial value is placed verbatim, so an initializer carrying x/z bits
// leaves the variable in an unknown state rather than coercing to 0.
TEST(VariableInitSim, FourStateInitializerPreservesXZ) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] v = 4'b10xz;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("v");
  ASSERT_NE(v, nullptr);
  EXPECT_FALSE(v->value.IsKnown());
}

// A negative initializer is stored as its two's-complement bit pattern in the
// declared width (here a 32-bit int).
TEST(VariableInitSim, SignedNegativeInitializer) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x = -5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0xFFFFFFFBull);
}

// The initialization has no duration: with no intervening assignment the
// value is unchanged when read at a later simulation time.
TEST(VariableInitSim, InitValuePersistsAcrossTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x = 7;\n"
      "  int snapshot;\n"
      "  initial #5 snapshot = x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* snap = f.ctx.FindVariable("snapshot");
  ASSERT_NE(snap, nullptr);
  EXPECT_EQ(snap->value.ToUint64(), 7u);
}

// §10.5's own example: `logic v = consta & constb;` where consta and constb
// are themselves variables carrying declaration initializers. Because static
// initialization runs in declaration order and completes before any procedure,
// v's initializer sees the already-initialized consta/constb and evaluates to
// their bitwise-AND. This drives the exact example shape end-to-end, unlike the
// literal-operand VarInitWithExpression case.
TEST(VariableInitSim, VarInitFromOtherInitializedVariables) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] consta = 8'hFC;\n"
      "  logic [7:0] constb = 8'h3F;\n"
      "  logic [7:0] v = consta & constb;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 0x3Cu);
}

// A variable initializer may name a parameter as its operand. The parameter is
// an elaboration-time constant resolved during static initialization (its
// storage is created before the variables that read it), so v receives the
// parameter's value. This exercises the param-resolution path, distinct from a
// literal or a plain-variable operand.
TEST(VariableInitSim, VarInitFromParameterOperand) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  parameter [7:0] P = 8'h3C;\n"
                      "  logic [7:0] v = P;\n"
                      "endmodule\n",
                      "v"),
            0x3Cu);
}

// The initializer operand may also be a localparam, and may appear inside a
// larger expression. Both the localparam resolution and the arithmetic happen
// during static initialization, before any procedure runs.
TEST(VariableInitSim, VarInitFromLocalparamInExpression) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  localparam [7:0] L = 8'd20;\n"
                      "  logic [7:0] v = L + 8'd3;\n"
                      "endmodule\n",
                      "v"),
            23u);
}

// Static initialization completes before any procedure starts, so an
// always_comb block evaluating at time 0 already sees the initialized value.
TEST(VariableInitSim, VarInitBeforeAlwaysCombBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a = 8'd9;\n"
      "  logic [7:0] o;\n"
      "  always_comb o = a + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* o = f.ctx.FindVariable("o");
  ASSERT_NE(o, nullptr);
  EXPECT_EQ(o->value.ToUint64(), 10u);
}

}  // namespace
