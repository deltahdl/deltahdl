// §9.4.2.2: Implicit event_expression list

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// 1. always @* with simple combinational AND gate: y = a & b.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarSimpleAnd) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always @* y = a & b;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    b = 8'h3C;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0x30u);
}

// ---------------------------------------------------------------------------
// 2. always @* with if-else selects the true branch.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarIfElseTrueBranch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b, y;\n"
      "  always @*\n"
      "    if (sel) y = a;\n"
      "    else y = b;\n"
      "  initial begin\n"
      "    a = 8'hAA;\n"
      "    b = 8'hBB;\n"
      "    sel = 1;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xAAu);
}

// ---------------------------------------------------------------------------
// 3. always @* with case statement selects the correct arm.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarCaseStatement) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] y;\n"
      "  always @*\n"
      "    case (sel)\n"
      "      2'b00: y = 8'h10;\n"
      "      2'b01: y = 8'h20;\n"
      "      2'b10: y = 8'h30;\n"
      "      default: y = 8'hFF;\n"
      "    endcase\n"
      "  initial begin\n"
      "    sel = 2'b10;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0x30u);
}

// ---------------------------------------------------------------------------
// 4. always @* sensitivity includes all RHS signals (a, b, c).
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarAllRhsSensitive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c, y;\n"
      "  always @* y = a + b + c;\n"
      "  initial begin\n"
      "    a = 8'h10;\n"
      "    b = 8'h20;\n"
      "    c = 8'h03;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // 0x10 + 0x20 + 0x03 = 0x33.
  EXPECT_EQ(y->value.ToUint64(), 0x33u);
}

// ---------------------------------------------------------------------------
// 5. always @* does NOT include LHS signal 'y' in sensitivity.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarLhsNotSensitive) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, y;\n"
      "  always @* y = a + 1;\n"
      "  initial begin\n"
      "    a = 8'h09;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // y = 0x09 + 1 = 0x0A. No infinite loop from self-triggering.
  EXPECT_EQ(y->value.ToUint64(), 0x0Au);
}

// ---------------------------------------------------------------------------
// 6. always @(*) form (with parentheses) is equivalent to @*.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarParenForm) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, y;\n"
      "  always @(*) y = a | b;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    b = 8'h0F;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xFFu);
}

// ---------------------------------------------------------------------------
// 7. always @* with ternary operator: sel ? a : b.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarTernaryOp) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic sel;\n"
      "  logic [7:0] a, b, y;\n"
      "  always @* y = sel ? a : b;\n"
      "  initial begin\n"
      "    a = 8'hDE;\n"
      "    b = 8'hAD;\n"
      "    sel = 0;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xADu);
}

// ---------------------------------------------------------------------------
// 8. always @* with concatenation -- all parts are sensitive.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarConcatenation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] hi, lo;\n"
      "  logic [7:0] y;\n"
      "  always @* y = {hi, lo};\n"
      "  initial begin\n"
      "    hi = 4'hC;\n"
      "    lo = 4'h3;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xC3u);
}

// ---------------------------------------------------------------------------
// 9. always @* with bit-select -- reading a single bit from a vector.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarBitSelect) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  logic [7:0] copy;\n"
      "  logic y;\n"
      "  always @* begin\n"
      "    copy = data;\n"
      "    y = data[5];\n"
      "  end\n"
      "  initial begin\n"
      "    data = 8'b0010_0000;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

// ---------------------------------------------------------------------------
// 10. always @* with part-select -- extracting a sub-range from a vector.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarPartSelect) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  logic [7:0] copy;\n"
      "  logic [3:0] y;\n"
      "  always @* begin\n"
      "    copy = data;\n"
      "    y = data[3:0];\n"
      "  end\n"
      "  initial begin\n"
      "    data = 8'hBE;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // data[3:0] of 0xBE = 0xE.
  EXPECT_EQ(y->value.ToUint64(), 0xEu);
}

// ---------------------------------------------------------------------------
// 11. always @* with function call -- function arguments are sensitive.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarFunctionCall) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  function logic [7:0] add3(input logic [7:0] x);\n"
      "    return x + 3;\n"
      "  endfunction\n"
      "  logic [7:0] a, y;\n"
      "  always @* y = add3(a);\n"
      "  initial begin\n"
      "    a = 8'h10;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // 0x10 + 3 = 0x13.
  EXPECT_EQ(y->value.ToUint64(), 0x13u);
}

// ---------------------------------------------------------------------------
// 12. always @* with nested expressions -- all leaf signals are sensitive.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarNestedExpr) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c, y;\n"
      "  always @* y = (a & b) | c;\n"
      "  initial begin\n"
      "    a = 8'hFF;\n"
      "    b = 8'h0F;\n"
      "    c = 8'hF0;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // (0xFF & 0x0F) | 0xF0 = 0x0F | 0xF0 = 0xFF.
  EXPECT_EQ(y->value.ToUint64(), 0xFFu);
}

// ---------------------------------------------------------------------------
// 13. always @* with multiple statements -- all read signals are sensitive.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarMultipleStmts) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, x, y;\n"
      "  always @* begin\n"
      "    x = a + 1;\n"
      "    y = b + 2;\n"
      "  end\n"
      "  initial begin\n"
      "    a = 8'h10;\n"
      "    b = 8'h20;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"x", 0x11u}, {"y", 0x22u}});
}

// ---------------------------------------------------------------------------
// 14. always @* with arithmetic operators (+, -, *, /).
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarArithmetic) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a, b, y;\n"
      "  always @* y = (a + b) * 2;\n"
      "  initial begin\n"
      "    a = 10;\n"
      "    b = 5;\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // (10 + 5) * 2 = 30.
  EXPECT_EQ(y->value.ToUint64(), 30u);
}

}  // namespace
