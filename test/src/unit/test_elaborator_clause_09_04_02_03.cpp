// §9.4.2.3: Conditional event controls

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §9.4.2.4: posedge clk iff enable=1 fires the event, body executes.
TEST(SimCh9e, PosedgeIffEnableTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, enable;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    clk = 0; enable = 1; count = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff enable)\n"
      "    count = count + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §9.4.2.4: posedge clk iff enable=0 suppresses the event.
TEST(SimCh9e, PosedgeIffEnableFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, enable;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    clk = 0; enable = 0; count = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff enable)\n"
      "    count = count + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §9.4.2.4: negedge clk iff enable=1 fires the event.
TEST(SimCh9e, NegedgeIffEnableTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, enable;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    clk = 1; enable = 1; count = 0;\n"
      "    #1 clk = 0;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(negedge clk iff enable)\n"
      "    count = count + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §9.4.2.4: negedge clk iff enable=0 suppresses the event.
TEST(SimCh9e, NegedgeIffEnableFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, enable;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    clk = 1; enable = 0; count = 0;\n"
      "    #1 clk = 0;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(negedge clk iff enable)\n"
      "    count = count + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §9.4.2.4: iff with logical-AND complex condition (a && b).
TEST(SimCh9e, IffComplexAndCondition) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, a, b;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    clk = 0; a = 1; b = 1; count = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff (a && b))\n"
      "    count = count + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §9.4.2.4: iff with logical-AND when one operand is false.
TEST(SimCh9e, IffComplexAndConditionOneFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, a, b;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    clk = 0; a = 1; b = 0; count = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff (a && b))\n"
      "    count = count + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("count");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §9.4.2.4: iff with comparison condition (count_val > 0).
TEST(SimCh9e, IffComparisonGreaterThanZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [31:0] count_val, result;\n"
      "  initial begin\n"
      "    clk = 0; count_val = 5; result = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff count_val > 0)\n"
      "    result = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// §9.4.2.4: iff with comparison when condition is false (count_val == 0).
TEST(SimCh9e, IffComparisonZeroSuppresses) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [31:0] count_val, result;\n"
      "  initial begin\n"
      "    clk = 0; count_val = 0; result = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff count_val > 0)\n"
      "    result = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §9.4.2.4: iff with bitwise-AND condition.
TEST(SimCh9e, IffBitwiseAndCondition) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] mask, enable;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    clk = 0; mask = 8'hFF; enable = 8'h01; result = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff (mask & enable))\n"
      "    result = 99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

// §9.4.2.4: iff with logical negation (!reset).
TEST(SimCh9e, IffLogicalNegation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, reset;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    clk = 0; reset = 0; result = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff !reset)\n"
      "    result = 77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

// §9.4.2.4: iff with !reset when reset=1 suppresses.
TEST(SimCh9e, IffLogicalNegationSuppresses) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, reset;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    clk = 0; reset = 1; result = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff !reset)\n"
      "    result = 77;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §9.4.2.4: Multiple events with different iff conditions.
TEST(SimCh9e, MultipleEventsWithDifferentIff) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, rst, en_clk, en_rst;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    clk = 0; rst = 1; en_clk = 1; en_rst = 0; result = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff en_clk, negedge rst iff en_rst)\n"
      "    result = result + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // Only posedge clk fires (en_clk=1), negedge rst suppressed (en_rst=0).
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

}  // namespace
