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

}  // namespace
