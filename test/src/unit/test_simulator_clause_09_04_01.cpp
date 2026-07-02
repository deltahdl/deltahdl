#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(DelayControlSim, DelayControlAdvancesTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    #10 x = 8'd42;\n"
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

TEST(DelayControlSim, DelayControlChained) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    #5 a = 8'd10;\n"
      "    #5 b = 8'd20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 10u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 20u);
}

TEST(DelayControlSim, DelayControlZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd1;\n"
      "    #0 x = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(DelayControlSim, DelayWithExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    #(5 + 5) x = 8'd99;\n"
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

TEST(DelayControlSim, DelayWithNullStatement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd1;\n"
      "    #10;\n"
      "    x = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

TEST(DelayControlSim, MultipleInitialBlocksWithDelays) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial #5 a = 8'd10;\n"
      "  initial #10 b = 8'd20;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("a")->value.ToUint64(), 10u);
  EXPECT_EQ(f.ctx.FindVariable("b")->value.ToUint64(), 20u);
}

TEST(DelayControlSim, NegativeDelayReinterpretedAsUnsignedTimeVariable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    d = -1;\n"
      "    #d x = 8'd99;\n"
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
  EXPECT_EQ(f.ctx.CurrentTime().ticks, ~uint64_t{0});
}

TEST(DelayControlSim, SpecparamPermittedInDelayExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  specify\n"
      "    specparam d = 7;\n"
      "  endspecify\n"
      "  logic [7:0] x;\n"
      "  initial #d x = 8'd55;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
  EXPECT_EQ(f.ctx.CurrentTime().ticks, 7u);
}

TEST(DelayControlSim, MultibitUnknownDelayTreatedAsZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd1;\n"
      "    #(4'b10xx) x = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.CurrentTime().ticks, 0u);
}

// §9.4.1 treats a high-impedance delay value the same as an unknown one: it is
// a zero delay. A single-bit z is non-discriminating because it carries no
// known nonzero bits, so this uses 4'b10zz whose known high bits are worth 8.
// Correct behavior forces a zero delay (time stays at 0); a raw-bits reading of
// the value would instead advance time by 8. This is the high-Z counterpart of
// MultibitUnknownDelayTreatedAsZero.
TEST(DelayControlSim, MultibitHighZDelayTreatedAsZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd1;\n"
      "    #(4'b10zz) x = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.CurrentTime().ticks, 0u);
}

TEST(DelayControlSim, NarrowSignedNegativeDelayReinterpretedAsTimeVariable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic signed [7:0] d;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    d = -1;\n"
      "    #d x = 8'd33;\n"
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
  EXPECT_EQ(f.ctx.CurrentTime().ticks, ~uint64_t{0});
}

// §9.4.1 lists a parameter among the operands permitted in a delay value. A
// parameter is not folded into a literal at the delay site: it is lowered to an
// instance-scoped runtime variable (Lowerer::LowerParams) that the delay
// expression resolves by name. This exercises that param-constant lookup path,
// which is distinct from the literal path covered by DelayControlAdvancesTime.
TEST(DelayControlSim, ParameterAsDelayValueAdvancesTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter P = 6;\n"
      "  logic [7:0] x;\n"
      "  initial #P x = 8'd55;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
  EXPECT_EQ(f.ctx.CurrentTime().ticks, 6u);
}

// §9.4.1 equally permits a localparam as the delay value. A localparam takes
// the same params list as a parameter but carries the is_localparam flag; it is
// still lowered to a runtime constant variable, so the delay must advance by
// its value. This is the localparam counterpart of the parameter delay form.
TEST(DelayControlSim, LocalparamAsDelayValueAdvancesTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam L = 8;\n"
      "  logic [7:0] x;\n"
      "  initial #L x = 8'd77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
  EXPECT_EQ(f.ctx.CurrentTime().ticks, 8u);
}

TEST(DelayControlSim, DelayExpressionReevaluatedAtEachExecution) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int d;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    d = 3;\n"
      "    #d x = 8'd1;\n"
      "    d = 7;\n"
      "    #d x = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.CurrentTime().ticks, 10u);
}

}  // namespace
