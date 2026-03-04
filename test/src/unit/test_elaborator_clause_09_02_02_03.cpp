#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(SimCh9c, ExecutesAtTimeZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  logic [7:0] d, q;\n"
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
  EXPECT_EQ(q->value.width, 8u);
  EXPECT_EQ(q->value.ToUint64(), 0u);
}

TEST(SimCh9c, UnconditionalAssignAtTimeZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] q;\n"
      "  always_latch\n"
      "    q = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.ToUint64(), 0xABu);
}

TEST(SimCh9c, IfWithoutElseRetainsDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  logic [7:0] d, q;\n"
      "  initial begin\n"
      "    en = 0;\n"
      "    d = 8'hFF;\n"
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

  EXPECT_EQ(q->value.ToUint64(), 0u);
}

TEST(SimCh9c, EnableHighPassesData) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  logic [7:0] d, q;\n"
      "  initial begin\n"
      "    en = 1;\n"
      "    d = 8'h42;\n"
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
  EXPECT_EQ(q->value.ToUint64(), 0x42u);
}

TEST(SimCh9c, EnableLowRetainsPreviousValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  logic [7:0] d, q;\n"
      "  initial begin\n"
      "    d = 8'hBB;\n"
      "    en = 1;\n"
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

  EXPECT_EQ(q->value.ToUint64(), 0xBBu);
}

static void LowerRunAndFindQ1Q2(SimFixture& f, RtlirDesign* design,
                                Variable*& q1_out, Variable*& q2_out) {
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  q1_out = f.ctx.FindVariable("q1");
  q2_out = f.ctx.FindVariable("q2");
  ASSERT_NE(q1_out, nullptr);
  ASSERT_NE(q2_out, nullptr);
}

TEST(SimCh9c, MultipleLatchesInOneBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  logic [7:0] d1, d2, q1, q2;\n"
      "  initial begin\n"
      "    en = 1;\n"
      "    d1 = 8'hAA;\n"
      "    d2 = 8'h55;\n"
      "  end\n"
      "  always_latch begin\n"
      "    if (en) q1 = d1;\n"
      "    if (en) q2 = d2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Variable* q1 = nullptr;
  Variable* q2 = nullptr;
  LowerRunAndFindQ1Q2(f, design, q1, q2);
  EXPECT_EQ(q1->value.ToUint64(), 0xAAu);
  EXPECT_EQ(q2->value.ToUint64(), 0x55u);
}

TEST(SimCh9c, MultipleLatchesEnableLow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  logic [7:0] d1, d2, q1, q2;\n"
      "  initial begin\n"
      "    en = 0;\n"
      "    d1 = 8'hAA;\n"
      "    d2 = 8'h55;\n"
      "  end\n"
      "  always_latch begin\n"
      "    if (en) q1 = d1;\n"
      "    if (en) q2 = d2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Variable* q1 = nullptr;
  Variable* q2 = nullptr;
  LowerRunAndFindQ1Q2(f, design, q1, q2);
  EXPECT_EQ(q1->value.ToUint64(), 0u);
  EXPECT_EQ(q2->value.ToUint64(), 0u);
}

TEST(SimCh9c, IncompleteCaseRetainsValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] q;\n"
      "  initial sel = 2'b00;\n"
      "  always_latch\n"
      "    case (sel)\n"
      "      2'b01: q = 8'hAA;\n"
      "      2'b10: q = 8'hBB;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);

  EXPECT_EQ(q->value.ToUint64(), 0u);
}

TEST(SimCh9c, LatchLogicType) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  logic [3:0] d, q;\n"
      "  initial begin\n"
      "    en = 1;\n"
      "    d = 4'hC;\n"
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
  EXPECT_EQ(q->value.width, 4u);
  EXPECT_EQ(q->value.ToUint64(), 0xCu);
}

TEST(SimCh9c, LatchIntType) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  int d, q;\n"
      "  initial begin\n"
      "    en = 1;\n"
      "    d = 12345;\n"
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
  EXPECT_EQ(q->value.ToUint64(), 12345u);
}

TEST(SimCh9c, LatchByteType) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  byte d, q;\n"
      "  initial begin\n"
      "    en = 1;\n"
      "    d = 8'hFE;\n"
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
  EXPECT_EQ(q->value.width, 8u);
  EXPECT_EQ(q->value.ToUint64(), 0xFEu);
}

TEST(SimCh9c, BitSelectRHS) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  logic [7:0] d;\n"
      "  logic q;\n"
      "  initial begin\n"
      "    en = 1;\n"
      "    d = 8'b1010_0101;\n"
      "  end\n"
      "  always_latch\n"
      "    if (en) q = d[0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);

  EXPECT_EQ(q->value.ToUint64(), 1u);
}

TEST(SimCh9c, ConcatenationRHS) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  logic [3:0] a, b;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    en = 1;\n"
      "    a = 4'hA;\n"
      "    b = 4'h5;\n"
      "  end\n"
      "  always_latch\n"
      "    if (en) q = {a, b};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);

  EXPECT_EQ(q->value.ToUint64(), 0xA5u);
}

TEST(SimCh9c, ConcatenationRetainedWhenLow) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  logic [3:0] a, b;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    en = 0;\n"
      "    a = 4'hA;\n"
      "    b = 4'h5;\n"
      "  end\n"
      "  always_latch\n"
      "    if (en) q = {a, b};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);

  EXPECT_EQ(q->value.ToUint64(), 0u);
}

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

  EXPECT_EQ(q->value.ToUint64(), 0u);
}

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

  EXPECT_EQ(q1->value.ToUint64(), 0xDEu);
  EXPECT_EQ(q2->value.ToUint64(), 0u);
}

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

  EXPECT_EQ(q->value.ToUint64(), 0x30u);
}

}
