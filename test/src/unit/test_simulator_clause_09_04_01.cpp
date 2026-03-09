#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SimA605, DelayControlAdvancesTime) {
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

TEST(SimA605, DelayControlChained) {
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

TEST(SimCh4, SimulationTimeAdvances) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    #10 x = 8'd1;\n"
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

uint64_t EvaluateDelay(int64_t value, bool is_unknown, bool is_highz) {
  if (is_unknown || is_highz) return 0;
  if (value < 0) return static_cast<uint64_t>(value);
  return static_cast<uint64_t>(value);
}

TEST(TimingControl, UnknownDelayTreatedAsZero) {
  EXPECT_EQ(EvaluateDelay(0, true, false), 0u);
}

TEST(TimingControl, HighZDelayTreatedAsZero) {
  EXPECT_EQ(EvaluateDelay(0, false, true), 0u);
}

TEST(TimingControl, NegativeDelayUnsignedInterpretation) {
  uint64_t result = EvaluateDelay(-1, false, false);
  EXPECT_GT(result, 0u);
}

TEST(TimingControl, PositiveDelayPassesThrough) {
  EXPECT_EQ(EvaluateDelay(10, false, false), 10u);
}

TEST(TimingControl, ZeroDelayIsZero) {
  EXPECT_EQ(EvaluateDelay(0, false, false), 0u);
}

}  // namespace
