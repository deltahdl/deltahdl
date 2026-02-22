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

struct SimCh9dFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, SimCh9dFixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

// ---------------------------------------------------------------------------
// 1. always @* with simple combinational AND gate: y = a & b.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarSimpleAnd) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
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

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0x30u);
}

// ---------------------------------------------------------------------------
// 2. always @* with if-else selects the true branch.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarIfElseTrueBranch) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
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

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xAAu);
}

// ---------------------------------------------------------------------------
// 3. always @* with case statement selects the correct arm.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarCaseStatement) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
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

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0x30u);
}

// ---------------------------------------------------------------------------
// 4. always @* sensitivity includes all RHS signals (a, b, c).
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarAllRhsSensitive) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
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

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // 0x10 + 0x20 + 0x03 = 0x33.
  EXPECT_EQ(y->value.ToUint64(), 0x33u);
}

// ---------------------------------------------------------------------------
// 5. always @* does NOT include LHS signal 'y' in sensitivity.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarLhsNotSensitive) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
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

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // y = 0x09 + 1 = 0x0A. No infinite loop from self-triggering.
  EXPECT_EQ(y->value.ToUint64(), 0x0Au);
}

// ---------------------------------------------------------------------------
// 6. always @(*) form (with parentheses) is equivalent to @*.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarParenForm) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
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

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xFFu);
}

// ---------------------------------------------------------------------------
// 7. always @* with ternary operator: sel ? a : b.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarTernaryOp) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
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

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xADu);
}

// ---------------------------------------------------------------------------
// 8. always @* with concatenation -- all parts are sensitive.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarConcatenation) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
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

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0xC3u);
}

// ---------------------------------------------------------------------------
// 9. always @* with bit-select -- reading a single bit from a vector.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarBitSelect) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
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

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

// ---------------------------------------------------------------------------
// 10. always @* with part-select -- extracting a sub-range from a vector.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarPartSelect) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
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

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // data[3:0] of 0xBE = 0xE.
  EXPECT_EQ(y->value.ToUint64(), 0xEu);
}

// ---------------------------------------------------------------------------
// 11. always @* with function call -- function arguments are sensitive.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarFunctionCall) {
  SimCh9dFixture f;
  auto *design =
      ElaborateSrc("module t;\n"
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

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // 0x10 + 3 = 0x13.
  EXPECT_EQ(y->value.ToUint64(), 0x13u);
}

// ---------------------------------------------------------------------------
// 12. always @* with nested expressions -- all leaf signals are sensitive.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarNestedExpr) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
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

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // (0xFF & 0x0F) | 0xF0 = 0x0F | 0xF0 = 0xFF.
  EXPECT_EQ(y->value.ToUint64(), 0xFFu);
}

// ---------------------------------------------------------------------------
// 13. always @* with multiple statements -- all read signals are sensitive.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarMultipleStmts) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
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
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *x = f.ctx.FindVariable("x");
  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(x, nullptr);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0x11u);
  EXPECT_EQ(y->value.ToUint64(), 0x22u);
}

// ---------------------------------------------------------------------------
// 14. always @* with arithmetic operators (+, -, *, /).
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarArithmetic) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
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

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // (10 + 5) * 2 = 30.
  EXPECT_EQ(y->value.ToUint64(), 30u);
}

// ---------------------------------------------------------------------------
// 15. always @* with bitwise operators (&, |, ^).
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarBitwiseOps) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a, b, c, y;\n"
                              "  always @* y = (a & b) ^ c;\n"
                              "  initial begin\n"
                              "    a = 8'hFF;\n"
                              "    b = 8'hAA;\n"
                              "    c = 8'h55;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // (0xFF & 0xAA) ^ 0x55 = 0xAA ^ 0x55 = 0xFF.
  EXPECT_EQ(y->value.ToUint64(), 0xFFu);
}

// ---------------------------------------------------------------------------
// 16. always @* with comparison operators (==, <).
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarComparison) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a, b;\n"
                              "  logic y;\n"
                              "  always @* y = (a > b);\n"
                              "  initial begin\n"
                              "    a = 8'h20;\n"
                              "    b = 8'h10;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // 0x20 > 0x10 is true = 1.
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

// ---------------------------------------------------------------------------
// 17. always @* with logical operators (&&, ||).
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarLogicalOps) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic a, b, y;\n"
                              "  always @* y = a && b;\n"
                              "  initial begin\n"
                              "    a = 1;\n"
                              "    b = 1;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

// ---------------------------------------------------------------------------
// 18. always @* with unary operators (~, !).
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarUnaryOps) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a, y;\n"
                              "  always @* y = ~a;\n"
                              "  initial begin\n"
                              "    a = 8'hA5;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // ~0xA5 = 0x5A in the low 8 bits; mask to declared width.
  EXPECT_EQ(y->value.ToUint64() & 0xFFu, 0x5Au);
}

// ---------------------------------------------------------------------------
// 19. always @* with multiple outputs computed from same inputs.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarMultipleOutputs) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a, b, sum, diff;\n"
                              "  always @* begin\n"
                              "    sum = a + b;\n"
                              "    diff = a - b;\n"
                              "  end\n"
                              "  initial begin\n"
                              "    a = 8'h30;\n"
                              "    b = 8'h10;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *sum = f.ctx.FindVariable("sum");
  auto *diff = f.ctx.FindVariable("diff");
  ASSERT_NE(sum, nullptr);
  ASSERT_NE(diff, nullptr);
  EXPECT_EQ(sum->value.ToUint64(), 0x40u);
  EXPECT_EQ(diff->value.ToUint64(), 0x20u);
}

// ---------------------------------------------------------------------------
// 20. always @* with local variable (not in sensitivity).
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarLocalVar) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a, b, y;\n"
                              "  always @* begin\n"
                              "    logic [7:0] tmp;\n"
                              "    tmp = a + b;\n"
                              "    y = tmp;\n"
                              "  end\n"
                              "  initial begin\n"
                              "    a = 8'h11;\n"
                              "    b = 8'h22;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0x33u);
}

// ---------------------------------------------------------------------------
// 21. always @* with begin-end block and sequential assignments.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarBeginEnd) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a, b, x, y;\n"
                              "  always @* begin\n"
                              "    x = a + 1;\n"
                              "    y = b + 2;\n"
                              "  end\n"
                              "  initial begin\n"
                              "    a = 8'h05;\n"
                              "    b = 8'h03;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *x = f.ctx.FindVariable("x");
  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(x, nullptr);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0x06u);
  EXPECT_EQ(y->value.ToUint64(), 0x05u);
}

// ---------------------------------------------------------------------------
// 22. always @* with nested if-else (priority encoder using full-signal reads).
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarPriorityEncoder) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [3:0] req;\n"
                              "  logic [1:0] grant;\n"
                              "  always @* begin\n"
                              "    if (req >= 4'd8) grant = 2'b11;\n"
                              "    else if (req >= 4'd4) grant = 2'b10;\n"
                              "    else if (req >= 4'd2) grant = 2'b01;\n"
                              "    else grant = 2'b00;\n"
                              "  end\n"
                              "  initial begin\n"
                              "    req = 4'd3;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *grant = f.ctx.FindVariable("grant");
  ASSERT_NE(grant, nullptr);
  // req = 3 >= 2, so grant = 2'b01 = 1.
  EXPECT_EQ(grant->value.ToUint64(), 1u);
}

// ---------------------------------------------------------------------------
// 23. always @* with case decode (address decoder pattern).
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarCaseDecode) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [1:0] addr;\n"
                              "  logic [3:0] sel;\n"
                              "  always @*\n"
                              "    case (addr)\n"
                              "      2'b00: sel = 4'b0001;\n"
                              "      2'b01: sel = 4'b0010;\n"
                              "      2'b10: sel = 4'b0100;\n"
                              "      2'b11: sel = 4'b1000;\n"
                              "    endcase\n"
                              "  initial begin\n"
                              "    addr = 2'b11;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *sel = f.ctx.FindVariable("sel");
  ASSERT_NE(sel, nullptr);
  // addr = 2'b11, so sel = 4'b1000 = 8.
  EXPECT_EQ(sel->value.ToUint64(), 8u);
}

// ---------------------------------------------------------------------------
// 24. Multiple always @* blocks have independent sensitivity and outputs.
// ---------------------------------------------------------------------------
TEST(SimCh9d, MultipleAlwaysStarIndependent) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a, b, c, d, x, y;\n"
                              "  always @* x = a & b;\n"
                              "  always @* y = c | d;\n"
                              "  initial begin\n"
                              "    a = 8'hFF;\n"
                              "    b = 8'h0F;\n"
                              "    c = 8'hA0;\n"
                              "    d = 8'h05;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *x = f.ctx.FindVariable("x");
  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(x, nullptr);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0x0Fu);
  EXPECT_EQ(y->value.ToUint64(), 0xA5u);
}

// ---------------------------------------------------------------------------
// 25. always @* equivalent to always_comb for simple combinational logic.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarEquivAlwaysComb) {
  SimCh9dFixture f_star;
  auto *d_star = ElaborateSrc("module t;\n"
                              "  logic [7:0] a, b, y;\n"
                              "  always @* y = a ^ b;\n"
                              "  initial begin\n"
                              "    a = 8'hAA;\n"
                              "    b = 8'h55;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f_star);
  ASSERT_NE(d_star, nullptr);

  Lowerer lowerer_star(f_star.ctx, f_star.arena, f_star.diag);
  lowerer_star.Lower(d_star);
  f_star.scheduler.Run();

  SimCh9dFixture f_comb;
  auto *d_comb = ElaborateSrc("module t;\n"
                              "  logic [7:0] a, b, y;\n"
                              "  always_comb y = a ^ b;\n"
                              "  initial begin\n"
                              "    a = 8'hAA;\n"
                              "    b = 8'h55;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f_comb);
  ASSERT_NE(d_comb, nullptr);

  Lowerer lowerer_comb(f_comb.ctx, f_comb.arena, f_comb.diag);
  lowerer_comb.Lower(d_comb);
  f_comb.scheduler.Run();

  auto *y_star = f_star.ctx.FindVariable("y");
  auto *y_comb = f_comb.ctx.FindVariable("y");
  ASSERT_NE(y_star, nullptr);
  ASSERT_NE(y_comb, nullptr);
  EXPECT_EQ(y_star->value.ToUint64(), y_comb->value.ToUint64());
}

// ---------------------------------------------------------------------------
// 26. always @* with type cast (signed').
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarTypeCast) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a;\n"
                              "  logic [31:0] y;\n"
                              "  always @* y = signed'(a);\n"
                              "  initial begin\n"
                              "    a = 8'hFF;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // 8'hFF sign-extended to 32 bits = 0xFFFFFFFF.
  EXPECT_EQ(y->value.ToUint64(), 0xFFFFFFFFu);
}

// ---------------------------------------------------------------------------
// 27. Verify correctness of combinational output set via initial block.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarCombOutputFromInitial) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [15:0] a, b, y;\n"
                              "  always @* y = a + b;\n"
                              "  initial begin\n"
                              "    a = 16'h1234;\n"
                              "    b = 16'h4321;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0x5555u);
}

// ---------------------------------------------------------------------------
// 28. Verify .width and .ToUint64() on always @* results (8-bit output).
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarResultWidthAndValue8) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a, y;\n"
                              "  always @* y = a;\n"
                              "  initial begin\n"
                              "    a = 8'hAB;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.width, 8u);
  EXPECT_EQ(y->value.ToUint64(), 0xABu);
}

// ---------------------------------------------------------------------------
// 29. Verify .width and .ToUint64() on always @(*) results (32-bit output).
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarParenResultWidth32) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [31:0] a, y;\n"
                              "  always @(*) y = a;\n"
                              "  initial begin\n"
                              "    a = 32'hDEADBEEF;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.width, 32u);
  EXPECT_EQ(y->value.ToUint64(), 0xDEADBEEFu);
}

// ---------------------------------------------------------------------------
// 30. always @* with logical NOT (!) on a multi-bit signal.
// ---------------------------------------------------------------------------
TEST(SimCh9d, AlwaysStarLogicalNot) {
  SimCh9dFixture f;
  auto *design = ElaborateSrc("module t;\n"
                              "  logic [7:0] a;\n"
                              "  logic y;\n"
                              "  always @* y = !a;\n"
                              "  initial begin\n"
                              "    a = 8'h00;\n"
                              "    #1 $finish;\n"
                              "  end\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto *y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  // !0 = 1.
  EXPECT_EQ(y->value.ToUint64(), 1u);
}
