
#include "simulation/lowerer.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

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

// §9.4.2.4: iff guard on both posedge and negedge in same list.
TEST(SimCh9e, IffOnBothEdgesInList) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, en_pos, en_neg;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    clk = 0; en_pos = 1; en_neg = 1; result = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 clk = 0;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff en_pos or negedge clk iff en_neg)\n"
      "    result = result + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // posedge at t=1 fires (en_pos=1), negedge at t=2 fires (en_neg=1).
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// §9.4.2.4: iff guard on posedge fires, negedge suppressed.
TEST(SimCh9e, IffPosedgeFiresNegedgeSuppressed) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, en_pos, en_neg;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    clk = 0; en_pos = 1; en_neg = 0; result = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 clk = 0;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff en_pos or negedge clk iff en_neg)\n"
      "    result = result + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // Only posedge fires (en_pos=1), negedge suppressed (en_neg=0).
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §9.4.2.4: iff condition variable changes between edges.
TEST(SimCh9e, IffConditionChanges) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, enable;\n"
      "  logic [31:0] count;\n"
      "  initial begin\n"
      "    clk = 0; enable = 0; count = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 clk = 0;\n"
      "    #1 enable = 1;\n"
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
  // First posedge at t=1: enable=0, suppressed.
  // Second posedge at t=4: enable=1, fires.
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §9.4.2.4: always_ff @(posedge clk iff en) with register update.
TEST(SimCh9e, AlwaysFFIffRegisterUpdate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, en;\n"
      "  logic [31:0] d, q;\n"
      "  initial begin\n"
      "    clk = 0; en = 1; d = 55; q = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always_ff @(posedge clk iff en)\n"
      "    q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("q");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

// §9.4.2.4: always_ff @(posedge clk iff en) suppressed when en=0.
TEST(SimCh9e, AlwaysFFIffSuppressed) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, en;\n"
      "  logic [31:0] d, q;\n"
      "  initial begin\n"
      "    clk = 0; en = 0; d = 55; q = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always_ff @(posedge clk iff en)\n"
      "    q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("q");
  ASSERT_NE(var, nullptr);
  // en=0 at posedge, so q should remain 0.
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §9.4.2.4: iff guard in always block with begin/end body.
TEST(SimCh9e, IffGuardAlwaysBlockBeginEnd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, en;\n"
      "  logic [31:0] a, b;\n"
      "  initial begin\n"
      "    clk = 0; en = 1; a = 0; b = 0;\n"
      "    #1 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff en) begin\n"
      "    a = 10;\n"
      "    b = 20;\n"
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
  EXPECT_EQ(a->value.ToUint64(), 10u);
  EXPECT_EQ(b->value.ToUint64(), 20u);
}

// §9.4.2.4: iff with edge on data signal (not just clock).
TEST(SimCh9e, IffEdgeOnDataSignal) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic data, valid;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    data = 0; valid = 1; result = 0;\n"
      "    #1 data = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge data iff valid)\n"
      "    result = 88;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 88u);
}

// §9.4.2.4: iff condition evaluated at time of edge (not earlier).
TEST(SimCh9e, IffConditionEvaluatedAtEdgeTime) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, enable;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    clk = 0; enable = 1; result = 0;\n"
      "    #1 enable = 0;\n"
      "    #0 clk = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff enable)\n"
      "    result = 33;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // enable=0 at time of posedge, so event should be suppressed.
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

// §9.4.2.4: iff with equality comparison (reset == 0).
TEST(SimCh9e, IffEqualityComparison) {
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
      "  always @(posedge clk iff reset == 0)\n"
      "    result = 66;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 66u);
}

// §9.4.2.4: Multiple signals, only some with iff guards.
TEST(SimCh9e, MixedIffAndNoIff) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, rst_n, en;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    clk = 0; rst_n = 1; en = 0; result = 0;\n"
      "    #1 rst_n = 0;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(posedge clk iff en or negedge rst_n)\n"
      "    result = result + 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  // posedge clk never occurs. negedge rst_n fires (no iff guard on it).
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// §9.4.2.4: iff with bit-select condition (enable[0]).
TEST(SimCh9e, IffBitSelectCondition) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] enable;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    clk = 0; enable = 8'h01; result = 0;\n"
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
  EXPECT_EQ(var->value.ToUint64(), 44u);
}

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
