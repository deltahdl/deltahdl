#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(AlwaysFfElaboration, TimingControlInAlwaysLatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch #5 if (en) q = d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AlwaysFfElaboration, ForkJoinInAlwaysLatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, a, b, q;\n"
      "  always_latch begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AlwaysFfElaboration, IncompleteIfNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch\n"
      "    if (en) q = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(AlwaysFfElaboration, CompleteIfElseWarnsNotLatched) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, a, b, q;\n"
      "  always_latch\n"
      "    if (en) q = a;\n"
      "    else q = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(AlwaysFfElaboration, CaseWithoutDefaultNoWarning) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic q;\n"
      "  always_latch\n"
      "    case (sel)\n"
      "      2'b00: q = 0;\n"
      "      2'b01: q = 1;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(AlwaysFfElaboration, CaseWithDefaultWarnsNotLatched) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic q;\n"
      "  always_latch\n"
      "    case (sel)\n"
      "      2'b00: q = 0;\n"
      "      2'b01: q = 1;\n"
      "      default: q = 0;\n"
      "    endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

TEST(AlwaysFfElaboration, AlwaysLatchElaboratesToCorrectKind) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch\n"
      "    if (en) q = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  bool found = false;
  for (auto& p : design->top_modules[0]->processes) {
    if (p.kind == RtlirProcessKind::kAlwaysLatch) found = true;
  }
  EXPECT_TRUE(found);
}

TEST(AlwaysFfElaboration, MultiDriverTwoAlwaysLatchErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic en, a, b, q;\n"
      "  always_latch if (en) q = a;\n"
      "  always_latch if (en) q = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(AlwaysLatchBasicSim, ExecutesAtTimeZero) {
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

TEST(AlwaysLatchBasicSim, UnconditionalAssignAtTimeZero) {
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

TEST(AlwaysLatchBasicSim, IfWithoutElseRetainsDefault) {
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

TEST(AlwaysLatchBasicSim, EnableHighPassesData) {
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

TEST(AlwaysLatchBasicSim, EnableLowRetainsPreviousValue) {
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

TEST(AlwaysLatchBasicSim, MultipleLatchesInOneBlock) {
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

TEST(AlwaysLatchBasicSim, MultipleLatchesEnableLow) {
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

TEST(AlwaysLatchBasicSim, IncompleteCaseRetainsValue) {
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

TEST(AlwaysLatchBasicSim, LatchLogicType) {
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

TEST(AlwaysLatchBasicSim, LatchIntType) {
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

TEST(AlwaysLatchBasicSim, LatchByteType) {
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

TEST(AlwaysLatchBasicSim, BitSelectRHS) {
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

TEST(AlwaysLatchBasicSim, ConcatenationRHS) {
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

TEST(AlwaysLatchBasicSim, ConcatenationRetainedWhenLow) {
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

TEST(AlwaysLatchBasicSim, NestedIfElseBothTrue) {
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

TEST(AlwaysLatchBasicSim, NestedIfElseInnerFalse) {
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

TEST(AlwaysLatchBasicSim, NestedIfElseOuterFalse) {
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

TEST(AlwaysLatchBasicSim, MultipleOutputsDifferentSources) {
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

TEST(AlwaysLatchBasicSim, MultipleOutputsIndependentEnables) {
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

TEST(AlwaysLatchBasicSim, OutputAvailableAfterRun) {
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

TEST(AlwaysLatchBasicSim, WidthVerificationSingleBit) {
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

TEST(AlwaysLatchBasicSim, Width32BitAndToUint64) {
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

TEST(AlwaysLatchBasicSim, BeginEndBlockWithArithmetic) {
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

}  // namespace
