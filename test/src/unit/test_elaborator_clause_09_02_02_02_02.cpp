// §9.2.2.2.2: always_comb compared to always @*

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// 1. always_comb executes at time 0 (initial evaluation).
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombExecutesAtTimeZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial a = 8'd0;\n"
      "  always_comb begin\n"
      "    result = a + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // a is explicitly 0, so result = 0 + 1 = 1.
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// ---------------------------------------------------------------------------
// 2. always_comb AND gate: result = a & b.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombAndGate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, result;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    b = 8'h3C;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = a & b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x30u);
}

// ---------------------------------------------------------------------------
// 3. always_comb OR gate: result = a | b.
// ---------------------------------------------------------------------------
TEST(SimCh9, AlwaysCombOrGate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, result;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    b = 8'h0F;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = a | b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

}  // namespace
