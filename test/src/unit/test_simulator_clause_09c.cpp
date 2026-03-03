// Non-LRM tests

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// =============================================================================
// §9.2.3: always_latch with ternary operator
// =============================================================================
// 20. Ternary operator in always_latch selects first operand.
TEST(SimCh9c, TernarySelectsFirst) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b, q;\n"
      "  initial begin\n"
      "    sel = 1;\n"
      "    a = 8'hCA;\n"
      "    b = 8'hFE;\n"
      "  end\n"
      "  always_latch\n"
      "    q = sel ? a : b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 0xCAu);
}

// 21. Ternary operator in always_latch selects second operand.
TEST(SimCh9c, TernarySelectsSecond) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b, q;\n"
      "  initial begin\n"
      "    sel = 0;\n"
      "    a = 8'hCA;\n"
      "    b = 8'hFE;\n"
      "  end\n"
      "  always_latch\n"
      "    q = sel ? a : b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 0xFEu);
}

// =============================================================================
// §9.2.3: always_latch with nested if-else
// =============================================================================
// 22. Nested if-else: outer condition true, inner condition true.
TEST(SimCh9c, NestedIfElseBothTrue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en, sel;\n"
      "  logic [7:0] a, b, q;\n"
      "  initial begin\n"
      "    en = 1;\n"
      "    sel = 1;\n"
      "    a = 8'h11;\n"
      "    b = 8'h22;\n"
      "  end\n"
      "  always_latch\n"
      "    if (en) begin\n"
      "      if (sel) q = a;\n"
      "      else q = b;\n"
      "    end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 0x11u);
}

// 23. Nested if-else: outer condition true, inner condition false.
TEST(SimCh9c, NestedIfElseInnerFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en, sel;\n"
      "  logic [7:0] a, b, q;\n"
      "  initial begin\n"
      "    en = 1;\n"
      "    sel = 0;\n"
      "    a = 8'h11;\n"
      "    b = 8'h22;\n"
      "  end\n"
      "  always_latch\n"
      "    if (en) begin\n"
      "      if (sel) q = a;\n"
      "      else q = b;\n"
      "    end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 0x22u);
}

// 24. Nested if-else: outer condition false, output retains value.
TEST(SimCh9c, NestedIfElseOuterFalse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en, sel;\n"
      "  logic [7:0] a, b, q;\n"
      "  initial begin\n"
      "    en = 0;\n"
      "    sel = 1;\n"
      "    a = 8'h11;\n"
      "    b = 8'h22;\n"
      "  end\n"
      "  always_latch\n"
      "    if (en) begin\n"
      "      if (sel) q = a;\n"
      "      else q = b;\n"
      "    end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  // en=0 means outer if not taken; q retains default 0.
  EXPECT_EQ(q->value.ToUint64(), 0u);
}

// =============================================================================
// §9.2.3: always_latch with multiple outputs
// =============================================================================
// 25. Multiple outputs assigned from different data sources.
TEST(SimCh9c, MultipleOutputsDifferentSources) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  logic [7:0] d1, d2, d3, q1, q2, q3;\n"
      "  initial begin\n"
      "    en = 1;\n"
      "    d1 = 8'h10;\n"
      "    d2 = 8'h20;\n"
      "    d3 = 8'h30;\n"
      "  end\n"
      "  always_latch begin\n"
      "    if (en) begin\n"
      "      q1 = d1;\n"
      "      q2 = d2;\n"
      "      q3 = d3;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q1 = f.ctx.FindVariable("q1");
  auto* q2 = f.ctx.FindVariable("q2");
  auto* q3 = f.ctx.FindVariable("q3");
  ASSERT_NE(q1, nullptr);
  ASSERT_NE(q2, nullptr);
  ASSERT_NE(q3, nullptr);
  EXPECT_EQ(q1->value.ToUint64(), 0x10u);
  EXPECT_EQ(q2->value.ToUint64(), 0x20u);
  EXPECT_EQ(q3->value.ToUint64(), 0x30u);
}

// 26. Multiple outputs with independent enable conditions.
TEST(SimCh9c, MultipleOutputsIndependentEnables) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en1, en2;\n"
      "  logic [7:0] d1, d2, q1, q2;\n"
      "  initial begin\n"
      "    en1 = 1;\n"
      "    en2 = 0;\n"
      "    d1 = 8'hDE;\n"
      "    d2 = 8'hAD;\n"
      "  end\n"
      "  always_latch begin\n"
      "    if (en1) q1 = d1;\n"
      "    if (en2) q2 = d2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q1 = f.ctx.FindVariable("q1");
  auto* q2 = f.ctx.FindVariable("q2");
  ASSERT_NE(q1, nullptr);
  ASSERT_NE(q2, nullptr);
  // en1=1, so q1=d1=0xDE. en2=0, so q2 retains default 0.
  EXPECT_EQ(q1->value.ToUint64(), 0xDEu);
  EXPECT_EQ(q2->value.ToUint64(), 0u);
}

// =============================================================================
// §9.2.3: always_latch output available after scheduler run
// =============================================================================
// 27. Output is available after scheduler.Run() completes.
TEST(SimCh9c, OutputAvailableAfterRun) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  logic [15:0] d, q;\n"
      "  initial begin\n"
      "    en = 1;\n"
      "    d = 16'hBEEF;\n"
      "  end\n"
      "  always_latch\n"
      "    if (en) q = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.width, 16u);
  EXPECT_EQ(q->value.ToUint64(), 0xBEEFu);
}

// 28. Verify .width on always_latch output with 1-bit result.
TEST(SimCh9c, WidthVerificationSingleBit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  logic d, q;\n"
      "  initial begin\n"
      "    en = 1;\n"
      "    d = 1;\n"
      "  end\n"
      "  always_latch\n"
      "    if (en) q = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.width, 1u);
  EXPECT_EQ(q->value.ToUint64(), 1u);
}

// =============================================================================
// §9.2.3: Verify .width and .ToUint64() on results
// =============================================================================
// 29. 32-bit always_latch output verifies width and value.
TEST(SimCh9c, Width32BitAndToUint64) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  logic [31:0] d, q;\n"
      "  initial begin\n"
      "    en = 1;\n"
      "    d = 32'hDEADBEEF;\n"
      "  end\n"
      "  always_latch\n"
      "    if (en) q = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.width, 32u);
  EXPECT_EQ(q->value.ToUint64(), 0xDEADBEEFu);
}

// 30. always_latch with begin/end block and arithmetic on RHS.
TEST(SimCh9c, BeginEndBlockWithArithmetic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  logic [7:0] a, b, q;\n"
      "  initial begin\n"
      "    en = 1;\n"
      "    a = 8'h10;\n"
      "    b = 8'h20;\n"
      "  end\n"
      "  always_latch begin\n"
      "    if (en) q = a + b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.width, 8u);
  // 0x10 + 0x20 = 0x30.
  EXPECT_EQ(q->value.ToUint64(), 0x30u);
}

}  // namespace
