// §9.2.2.3: Latched logic always_latch procedure

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// =============================================================================
// §9.2.3: always_latch executes at time 0
// The always_latch procedure executes once automatically at time 0.
// =============================================================================
// 1. always_latch body executes at time 0 with default variable values.
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

  // en defaults to 0, so q should retain its default value of 0.
  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.width, 8u);
  EXPECT_EQ(q->value.ToUint64(), 0u);
}

// 2. always_latch with unconditional assignment sets output at time 0.
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

// =============================================================================
// §9.2.3: always_latch with if-without-else creates latch behavior
// When the enable condition is false, the output retains its previous value.
// =============================================================================
// 3. if-without-else: enable low retains default (zero) value.
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
  // en=0, so always_latch does not assign q; q retains 0.
  EXPECT_EQ(q->value.ToUint64(), 0u);
}

// 4. if-without-else: enable high passes data through.
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

// 5. Enable low retains previous value set by initial block ordering.
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
  // en=1, d=0xBB, so q = 0xBB.
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

// =============================================================================
// §9.2.3: Multiple latches in one always_latch block
// =============================================================================
// 6. Two independent latches in one always_latch begin/end block.
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

// 7. Multiple latches with enable low: both retain default 0.
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

// =============================================================================
// §9.2.3: always_latch with incomplete case creates latch
// =============================================================================
// 8. Incomplete case (no default) retains value for unmatched selectors.
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
  // sel=0 matches no case item; q retains default 0.
  EXPECT_EQ(q->value.ToUint64(), 0u);
}

// =============================================================================
// §9.2.3: always_latch with different data types
// =============================================================================
// 11. always_latch with logic type.
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

}  // namespace
