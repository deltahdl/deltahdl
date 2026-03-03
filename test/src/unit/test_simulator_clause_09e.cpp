// Non-LRM tests

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §9.4.2.4: iff with bit-select zero suppresses.
TEST(SimCh9e, IffBitSelectZeroSuppresses) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] enable;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    clk = 0; enable = 8'hFE; result = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff enable[0])\n"
      "    result = 44;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // enable[0] = 0, so event suppressed.
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §9.4.2.4: iff guard preserves previous value when suppressed.
TEST(SimCh9e, IffPreservesPreviousValueWhenSuppressed) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, en;\n"
      "  logic [31:0] q;\n"
      "  initial begin\n"
      "    clk = 0; en = 1; q = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 clk = 0;\n"
      "    #1 en = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff en)\n"
      "    q = q + 10;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("q");
  ASSERT_NE(var, nullptr);
  // First posedge (t=1, en=1): q = 0+10 = 10.
  // Second posedge (t=4, en=0): suppressed, q stays 10.
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

// §9.4.2.4: Verify result .width is correct after iff-guarded update.
TEST(SimCh9e, ResultWidthAfterIffUpdate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, en;\n"
      "  logic [15:0] result;\n"
      "  initial begin\n"
      "    clk = 0; en = 1; result = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff en)\n"
      "    result = 16'hABCD;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 16u);
  EXPECT_EQ(var->value.ToUint64(), 0xABCDu);
}

// §9.4.2.4: Verify .width and .ToUint64() on 8-bit result.
TEST(SimCh9e, ResultWidth8BitAfterIffUpdate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, en;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    clk = 0; en = 1; result = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff en)\n"
      "    result = 8'hFF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
}

// §9.4.2.4: iff with logical-OR condition.
TEST(SimCh9e, IffLogicalOrCondition) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, a, b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    clk = 0; a = 0; b = 1; result = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff (a || b))\n"
      "    result = 55;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

// §9.4.2.4: iff with not-equal comparison (state != 0).
TEST(SimCh9e, IffNotEqualComparison) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [1:0] state;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    clk = 0; state = 2'b01; result = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff state != 0)\n"
      "    result = 22;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 22u);
}

// §9.4.2.4: iff in always block with nonblocking assignment.
TEST(SimCh9e, IffAlwaysBlockNba) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, en;\n"
      "  logic [31:0] q;\n"
      "  initial begin\n"
      "    clk = 0; en = 1; q = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff en)\n"
      "    q <= 123;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("q");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 123u);
}

}  // namespace
