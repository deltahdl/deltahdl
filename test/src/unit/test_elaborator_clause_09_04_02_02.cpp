#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(AlwaysStarSim, AlwaysStarSimpleAnd) {
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

TEST(AlwaysStarSim, AlwaysStarIfElseTrueBranch) {
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

TEST(AlwaysStarSim, AlwaysStarCaseStatement) {
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

TEST(AlwaysStarSim, AlwaysStarAllRhsSensitive) {
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

  EXPECT_EQ(y->value.ToUint64(), 0x33u);
}

TEST(AlwaysStarSim, AlwaysStarLhsNotSensitive) {
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

  EXPECT_EQ(y->value.ToUint64(), 0x0Au);
}

TEST(AlwaysStarSim, AlwaysStarParenForm) {
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

TEST(AlwaysStarSim, AlwaysStarTernaryOp) {
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

TEST(AlwaysStarSim, AlwaysStarConcatenation) {
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

TEST(AlwaysStarSim, AlwaysStarBitSelect) {
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

TEST(AlwaysStarSim, AlwaysStarPartSelect) {
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

  EXPECT_EQ(y->value.ToUint64(), 0xEu);
}

TEST(AlwaysStarSim, AlwaysStarFunctionCall) {
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

  EXPECT_EQ(y->value.ToUint64(), 0x13u);
}

TEST(AlwaysStarSim, AlwaysStarNestedExpr) {
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

  EXPECT_EQ(y->value.ToUint64(), 0xFFu);
}

TEST(AlwaysStarSim, AlwaysStarMultipleStmts) {
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

TEST(AlwaysStarSim, AlwaysStarArithmetic) {
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

  EXPECT_EQ(y->value.ToUint64(), 30u);
}

TEST(AlwaysStarSim, AlwaysStarBitwiseOps) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
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

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);

  EXPECT_EQ(y->value.ToUint64(), 0xFFu);
}

TEST(AlwaysStarSim, AlwaysStarComparison) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
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

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);

  EXPECT_EQ(y->value.ToUint64(), 1u);
}

TEST(AlwaysStarSim, AlwaysStarLogicalOps) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
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

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 1u);
}

TEST(AlwaysStarSim, AlwaysStarUnaryOps) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
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

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);

  EXPECT_EQ(y->value.ToUint64() & 0xFFu, 0x5Au);
}

TEST(AlwaysStarSim, AlwaysStarMultipleOutputs) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
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

  auto* sum = f.ctx.FindVariable("sum");
  auto* diff = f.ctx.FindVariable("diff");
  ASSERT_NE(sum, nullptr);
  ASSERT_NE(diff, nullptr);
  EXPECT_EQ(sum->value.ToUint64(), 0x40u);
  EXPECT_EQ(diff->value.ToUint64(), 0x20u);
}

TEST(AlwaysStarSim, AlwaysStarLocalVar) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
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

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0x33u);
}

TEST(AlwaysStarSim, AlwaysStarPriorityEncoder) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
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

  auto* grant = f.ctx.FindVariable("grant");
  ASSERT_NE(grant, nullptr);

  EXPECT_EQ(grant->value.ToUint64(), 1u);
}

TEST(AlwaysStarSim, AlwaysStarCaseDecode) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
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

  auto* sel = f.ctx.FindVariable("sel");
  ASSERT_NE(sel, nullptr);

  EXPECT_EQ(sel->value.ToUint64(), 8u);
}

TEST(AlwaysStarSim, MultipleAlwaysStarIndependent) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
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

  auto* x = f.ctx.FindVariable("x");
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(x, nullptr);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 0x0Fu);
  EXPECT_EQ(y->value.ToUint64(), 0xA5u);
}

TEST(AlwaysStarSim, AlwaysStarCombOutputFromInitial) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
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

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0x5555u);
}

TEST(AlwaysStarSim, AlwaysStarResultWidthAndValue8) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
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

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.width, 8u);
  EXPECT_EQ(y->value.ToUint64(), 0xABu);
}

TEST(AlwaysStarSim, AlwaysStarParenResultWidth32) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
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

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.width, 32u);
  EXPECT_EQ(y->value.ToUint64(), 0xDEADBEEFu);
}

TEST(AlwaysStarElab, PlainAlwaysWithStarSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  always @(*) b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  EXPECT_FALSE(mod->processes[0].sensitivity.empty());
}

// §9.4.2.2 Example 5: LHS index variable included in sensitivity.
// y[a] = !en  →  sensitivity includes 'a' (index) and 'en' (RHS).
TEST(AlwaysStarElab, LhsIndexVarInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] y;\n"
      "  logic [2:0] a;\n"
      "  logic en;\n"
      "  always @* begin\n"
      "    y = 8'hff;\n"
      "    y[a] = !en;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  auto& sens = mod->processes[0].sensitivity;
  std::unordered_set<std::string> names;
  for (const auto& ev : sens) {
    if (ev.signal && ev.signal->kind == ExprKind::kIdentifier)
      names.insert(std::string(ev.signal->text));
  }
  EXPECT_TRUE(names.count("en")) << "en (RHS) must be in sensitivity";
  EXPECT_TRUE(names.count("a")) << "a (LHS index) must be in sensitivity";
  EXPECT_FALSE(names.count("y")) << "y (pure LHS) must not be in sensitivity";
}

// §9.4.2.2 Example 2: Variables appearing on both LHS and RHS (read-after-write
// intermediates at module scope) are included in the sensitivity list.
TEST(AlwaysStarElab, ReadAfterWriteIntermediateInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b, c, d;\n"
      "  logic tmp1, tmp2, y;\n"
      "  always @* begin\n"
      "    tmp1 = a & b;\n"
      "    tmp2 = c & d;\n"
      "    y = tmp1 | tmp2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  auto& sens = mod->processes[0].sensitivity;
  std::unordered_set<std::string> names;
  for (const auto& ev : sens) {
    if (ev.signal && ev.signal->kind == ExprKind::kIdentifier)
      names.insert(std::string(ev.signal->text));
  }
  EXPECT_TRUE(names.count("a"));
  EXPECT_TRUE(names.count("b"));
  EXPECT_TRUE(names.count("c"));
  EXPECT_TRUE(names.count("d"));
  EXPECT_TRUE(names.count("tmp1"))
      << "tmp1 (read-after-write intermediate) must be in sensitivity";
  EXPECT_TRUE(names.count("tmp2"))
      << "tmp2 (read-after-write intermediate) must be in sensitivity";
}

// Variable used on both LHS and RHS of same assignment (read-modify-write).
TEST(AlwaysStarElab, ReadModifyWriteInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  always @* begin\n"
      "    a = a + 1;\n"
      "    b = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  auto& sens = mod->processes[0].sensitivity;
  std::unordered_set<std::string> names;
  for (const auto& ev : sens) {
    if (ev.signal && ev.signal->kind == ExprKind::kIdentifier)
      names.insert(std::string(ev.signal->text));
  }
  EXPECT_TRUE(names.count("a"))
      << "a (appears on RHS) must be in sensitivity even though also on LHS";
}

// §9.4.2.2 Example 6: Case item expressions include variables in sensitivity.
// case (1'b1) state[IDLE]: ...  →  'state' is in sensitivity.
TEST(AlwaysStarElab, CaseItemVarsInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0] state, next;\n"
      "  logic go;\n"
      "  always @* begin\n"
      "    next = 4'b0;\n"
      "    case (1'b1)\n"
      "      state[0]: if (go) next[1] = 1'b1;\n"
      "                else    next[0] = 1'b1;\n"
      "      state[1]:         next[2] = 1'b1;\n"
      "      state[2]:         next[3] = 1'b1;\n"
      "      state[3]:         next[0] = 1'b1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  auto& sens = mod->processes[0].sensitivity;
  std::unordered_set<std::string> names;
  for (const auto& ev : sens) {
    if (ev.signal && ev.signal->kind == ExprKind::kIdentifier)
      names.insert(std::string(ev.signal->text));
  }
  EXPECT_TRUE(names.count("state"))
      << "state (case item expression) must be in sensitivity";
  EXPECT_TRUE(names.count("go"))
      << "go (conditional expr) must be in sensitivity";
}

// Conditional (if) expression is in sensitivity, not just RHS.
TEST(AlwaysStarElab, ConditionalExprInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic sel, a, b, y;\n"
      "  always @* begin\n"
      "    if (sel) y = a;\n"
      "    else     y = b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  auto& sens = mod->processes[0].sensitivity;
  std::unordered_set<std::string> names;
  for (const auto& ev : sens) {
    if (ev.signal && ev.signal->kind == ExprKind::kIdentifier)
      names.insert(std::string(ev.signal->text));
  }
  EXPECT_TRUE(names.count("sel"))
      << "sel (conditional expr) must be in sensitivity";
  EXPECT_TRUE(names.count("a"));
  EXPECT_TRUE(names.count("b"));
  EXPECT_FALSE(names.count("y")) << "y (pure LHS) must not be in sensitivity";
}

// Case selector expression is in sensitivity.
TEST(AlwaysStarElab, CaseSelectorExprInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [7:0] y;\n"
      "  always @(*) begin\n"
      "    case (sel)\n"
      "      2'b00: y = 8'h10;\n"
      "      2'b01: y = 8'h20;\n"
      "      default: y = 8'hFF;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  auto& sens = mod->processes[0].sensitivity;
  std::unordered_set<std::string> names;
  for (const auto& ev : sens) {
    if (ev.signal && ev.signal->kind == ExprKind::kIdentifier)
      names.insert(std::string(ev.signal->text));
  }
  EXPECT_TRUE(names.count("sel"))
      << "sel (case selector) must be in sensitivity";
  EXPECT_FALSE(names.count("y")) << "y (pure LHS) must not be in sensitivity";
}

// Subroutine argument is in sensitivity.
TEST(AlwaysStarElab, SubroutineArgInSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function logic [7:0] inc(input logic [7:0] x);\n"
      "    return x + 1;\n"
      "  endfunction\n"
      "  logic [7:0] a, y;\n"
      "  always @* y = inc(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  auto& sens = mod->processes[0].sensitivity;
  std::unordered_set<std::string> names;
  for (const auto& ev : sens) {
    if (ev.signal && ev.signal->kind == ExprKind::kIdentifier)
      names.insert(std::string(ev.signal->text));
  }
  EXPECT_TRUE(names.count("a"))
      << "a (subroutine arg) must be in sensitivity";
  EXPECT_FALSE(names.count("y")) << "y (pure LHS) must not be in sensitivity";
}

// Block-local variables are excluded from sensitivity.
TEST(AlwaysStarElab, BlockLocalExcludedFromSensitivity) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b, y;\n"
      "  always @* begin\n"
      "    logic [7:0] tmp;\n"
      "    tmp = a + b;\n"
      "    y = tmp;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->processes.size(), 1u);
  auto& sens = mod->processes[0].sensitivity;
  std::unordered_set<std::string> names;
  for (const auto& ev : sens) {
    if (ev.signal && ev.signal->kind == ExprKind::kIdentifier)
      names.insert(std::string(ev.signal->text));
  }
  EXPECT_TRUE(names.count("a"));
  EXPECT_TRUE(names.count("b"));
  EXPECT_FALSE(names.count("tmp"))
      << "tmp (block-local) must not be in sensitivity";
  EXPECT_FALSE(names.count("y")) << "y (pure LHS) must not be in sensitivity";
}

// @* and @(*) produce identical sensitivity lists.
TEST(AlwaysStarElab, AtStarAndAtStarParenEquivalent) {
  ElabFixture f1;
  auto* d1 = ElaborateSrc(
      "module m;\n"
      "  logic a, b, y;\n"
      "  always @* y = a & b;\n"
      "endmodule\n",
      f1);
  ElabFixture f2;
  auto* d2 = ElaborateSrc(
      "module m;\n"
      "  logic a, b, y;\n"
      "  always @(*) y = a & b;\n"
      "endmodule\n",
      f2);
  ASSERT_NE(d1, nullptr);
  ASSERT_NE(d2, nullptr);
  EXPECT_FALSE(f1.has_errors);
  EXPECT_FALSE(f2.has_errors);
  auto& s1 = d1->top_modules[0]->processes[0].sensitivity;
  auto& s2 = d2->top_modules[0]->processes[0].sensitivity;
  EXPECT_EQ(s1.size(), s2.size());
  std::unordered_set<std::string> n1, n2;
  for (const auto& ev : s1)
    if (ev.signal) n1.insert(std::string(ev.signal->text));
  for (const auto& ev : s2)
    if (ev.signal) n2.insert(std::string(ev.signal->text));
  EXPECT_EQ(n1, n2);
}

}  // namespace
