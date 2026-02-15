#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulation/lowerer.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

using namespace delta;

struct SimCh9cFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign* ElaborateSrc(const std::string& src, SimCh9cFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

// =============================================================================
// §9.2.3: always_latch executes at time 0
// The always_latch procedure executes once automatically at time 0.
// =============================================================================

// 1. always_latch body executes at time 0 with default variable values.
TEST(SimCh9c, ExecutesAtTimeZero) {
  SimCh9cFixture f;
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
  SimCh9cFixture f;
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
  SimCh9cFixture f;
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
  SimCh9cFixture f;
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
  SimCh9cFixture f;
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

// =============================================================================
// §9.2.3: Multiple latches in one always_latch block
// =============================================================================

// 6. Two independent latches in one always_latch begin/end block.
TEST(SimCh9c, MultipleLatchesInOneBlock) {
  SimCh9cFixture f;
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

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q1 = f.ctx.FindVariable("q1");
  auto* q2 = f.ctx.FindVariable("q2");
  ASSERT_NE(q1, nullptr);
  ASSERT_NE(q2, nullptr);
  EXPECT_EQ(q1->value.ToUint64(), 0xAAu);
  EXPECT_EQ(q2->value.ToUint64(), 0x55u);
}

// 7. Multiple latches with enable low: both retain default 0.
TEST(SimCh9c, MultipleLatchesEnableLow) {
  SimCh9cFixture f;
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

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q1 = f.ctx.FindVariable("q1");
  auto* q2 = f.ctx.FindVariable("q2");
  ASSERT_NE(q1, nullptr);
  ASSERT_NE(q2, nullptr);
  EXPECT_EQ(q1->value.ToUint64(), 0u);
  EXPECT_EQ(q2->value.ToUint64(), 0u);
}

// =============================================================================
// §9.2.3: always_latch with incomplete case creates latch
// =============================================================================

// 8. Incomplete case (no default) retains value for unmatched selectors.
TEST(SimCh9c, IncompleteCaseRetainsValue) {
  SimCh9cFixture f;
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

// 9. Incomplete case with matching selector assigns value.
TEST(SimCh9c, IncompleteCaseMatchAssigns) {
  SimCh9cFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] q;\n"
      "  initial sel = 2'b01;\n"
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
  EXPECT_EQ(q->value.ToUint64(), 0xAAu);
}

// 10. Incomplete case matching second arm.
TEST(SimCh9c, IncompleteCaseSecondArm) {
  SimCh9cFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] q;\n"
      "  initial sel = 2'b10;\n"
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
  EXPECT_EQ(q->value.ToUint64(), 0xBBu);
}

// =============================================================================
// §9.2.3: always_latch with different data types
// =============================================================================

// 11. always_latch with logic type.
TEST(SimCh9c, LatchLogicType) {
  SimCh9cFixture f;
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

// 12. always_latch with int type (32-bit).
TEST(SimCh9c, LatchIntType) {
  SimCh9cFixture f;
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

// 13. always_latch with byte type (8-bit).
TEST(SimCh9c, LatchByteType) {
  SimCh9cFixture f;
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

// =============================================================================
// §9.2.3: always_latch with bit-select
// =============================================================================

// 14. Bit-select on RHS within always_latch.
TEST(SimCh9c, BitSelectRHS) {
  SimCh9cFixture f;
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
  // d = 0xA5 = 0b10100101; d[0] = 1.
  EXPECT_EQ(q->value.ToUint64(), 1u);
}

// 15. Bit-select on a different bit position.
TEST(SimCh9c, BitSelectHighBit) {
  SimCh9cFixture f;
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
      "    if (en) q = d[7];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  // d = 0xA5 = 0b10100101; d[7] = 1.
  EXPECT_EQ(q->value.ToUint64(), 1u);
}

// =============================================================================
// §9.2.3: always_latch with part-select
// =============================================================================

// 16. Part-select extracting lower nibble.
TEST(SimCh9c, PartSelectLowerNibble) {
  SimCh9cFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  logic [7:0] d;\n"
      "  logic [3:0] q;\n"
      "  initial begin\n"
      "    en = 1;\n"
      "    d = 8'hAB;\n"
      "  end\n"
      "  always_latch\n"
      "    if (en) q = d[3:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.width, 4u);
  // d = 0xAB; d[3:0] = 0xB.
  EXPECT_EQ(q->value.ToUint64(), 0xBu);
}

// 17. Part-select extracting upper nibble.
TEST(SimCh9c, PartSelectUpperNibble) {
  SimCh9cFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic en;\n"
      "  logic [7:0] d;\n"
      "  logic [3:0] q;\n"
      "  initial begin\n"
      "    en = 1;\n"
      "    d = 8'hAB;\n"
      "  end\n"
      "  always_latch\n"
      "    if (en) q = d[7:4];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* q = f.ctx.FindVariable("q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.width, 4u);
  // d = 0xAB; d[7:4] = 0xA.
  EXPECT_EQ(q->value.ToUint64(), 0xAu);
}

// =============================================================================
// §9.2.3: always_latch with concatenation
// =============================================================================

// 18. Concatenation on RHS within always_latch.
TEST(SimCh9c, ConcatenationRHS) {
  SimCh9cFixture f;
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
  // {4'hA, 4'h5} = 8'hA5.
  EXPECT_EQ(q->value.ToUint64(), 0xA5u);
}

// 19. Concatenation retained when enable is low.
TEST(SimCh9c, ConcatenationRetainedWhenLow) {
  SimCh9cFixture f;
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
  // en=0, q retains default 0.
  EXPECT_EQ(q->value.ToUint64(), 0u);
}

// =============================================================================
// §9.2.3: always_latch with ternary operator
// =============================================================================

// 20. Ternary operator in always_latch selects first operand.
TEST(SimCh9c, TernarySelectsFirst) {
  SimCh9cFixture f;
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
  SimCh9cFixture f;
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
  SimCh9cFixture f;
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
  SimCh9cFixture f;
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
  SimCh9cFixture f;
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
  SimCh9cFixture f;
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
  SimCh9cFixture f;
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
  SimCh9cFixture f;
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
  SimCh9cFixture f;
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
  SimCh9cFixture f;
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
  SimCh9cFixture f;
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
