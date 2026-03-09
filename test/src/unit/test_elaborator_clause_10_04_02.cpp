#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(Lowerer, NbaDefersUpdate) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    x <= 42;\n"
      "    x = x;  // read x: should still be 0 (X→0), not 42\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(Lowerer, NbaAppliesToValue) {
  LowerFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a, b;\n"
      "  initial begin\n"
      "    a <= 10;\n"
      "    b <= 20;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 10u}, {"b", 20u}});
}

TEST(SimCh10b, SimpleNBA) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a;\n"
      "  initial begin\n"
      "    a <= 5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

TEST(SimCh10b, NBADeferredUpdate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a;\n"
      "  logic [31:0] b;\n"
      "  initial begin\n"
      "    a = 10;\n"
      "    a <= 20;\n"
      "    b = a;\n"
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

  EXPECT_EQ(b->value.ToUint64(), 10u);

  EXPECT_EQ(a->value.ToUint64(), 20u);
}

TEST(SimCh10b, MultipleNBASameVarLastWins) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a;\n"
      "  initial begin\n"
      "    a <= 1;\n"
      "    a <= 2;\n"
      "    a <= 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(SimCh10b, NBASwapPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a;\n"
      "  logic [31:0] b;\n"
      "  initial begin\n"
      "    a = 10;\n"
      "    b = 20;\n"
      "    a <= b;\n"
      "    b <= a;\n"
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

  EXPECT_EQ(a->value.ToUint64(), 20u);
  EXPECT_EQ(b->value.ToUint64(), 10u);
}

TEST(SimCh10b, NBAExpressionRHS) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a;\n"
      "  logic [31:0] b;\n"
      "  initial begin\n"
      "    a = 7;\n"
      "    b <= a + 3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(SimCh10b, NBABitSelectLHS) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'b0000_0000;\n"
      "    a[3] <= 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("a");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 8u);
}

TEST(SimCh10b, NBAPartSelectLHS) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'h00;\n"
      "    a[3:0] <= 4'hF;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("a");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

TEST(SimCh10b, NBAConcatenationRHS) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] hi;\n"
      "  logic [3:0] lo;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    hi = 4'hA;\n"
      "    lo = 4'h5;\n"
      "    result <= {hi, lo};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

TEST(SimCh10b, NBATernaryRHS) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] sel;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    sel = 1;\n"
      "    result <= sel ? 42 : 99;\n"
      "  end\n"
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

TEST(SimCh10b, NBAInAlwaysFF) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  logic [31:0] q;\n"
      "  logic [31:0] d;\n"
      "  initial begin\n"
      "    d = 77;\n"
      "    clk = 0;\n"
      "    #1 clk = 1;\n"
      "  end\n"
      "  always_ff @(posedge clk) begin\n"
      "    q <= d;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("q");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 77u);
}

TEST(SimCh10b, NBAInInitialBlock) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    x <= 123;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 123u);
}

TEST(SimCh10b, NBAWithIfElse) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a;\n"
      "  logic [31:0] b;\n"
      "  logic cond;\n"
      "  initial begin\n"
      "    cond = 0;\n"
      "    if (cond)\n"
      "      a <= 100;\n"
      "    else\n"
      "      a <= 200;\n"
      "    cond = 1;\n"
      "    if (cond)\n"
      "      b <= 300;\n"
      "    else\n"
      "      b <= 400;\n"
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

  EXPECT_EQ(a->value.ToUint64(), 200u);

  EXPECT_EQ(b->value.ToUint64(), 300u);
}

TEST(SimCh10b, NBAWithCase) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] sel;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    sel = 2;\n"
      "    case (sel)\n"
      "      0: result <= 10;\n"
      "      1: result <= 20;\n"
      "      2: result <= 30;\n"
      "      default: result <= 40;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(SimCh10b, NBAInForLoop) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] acc;\n"
      "  initial begin\n"
      "    acc = 0;\n"
      "    for (int i = 0; i < 5; i = i + 1) begin\n"
      "      acc <= acc + 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("acc");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(SimCh10b, NBAFunctionCallRHS) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] result;\n"
      "  function int double_val(int x);\n"
      "    return x * 2;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    result <= double_val(21);\n"
      "  end\n"
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

TEST(SimCh10b, NBAPipelinePattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] in_val;\n"
      "  logic [31:0] stage1;\n"
      "  logic [31:0] stage2;\n"
      "  initial begin\n"
      "    in_val = 99;\n"
      "    stage1 = 55;\n"
      "    stage2 = 0;\n"
      "    stage2 <= stage1;\n"
      "    stage1 <= in_val;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* s1 = f.ctx.FindVariable("stage1");
  auto* s2 = f.ctx.FindVariable("stage2");
  ASSERT_NE(s1, nullptr);
  ASSERT_NE(s2, nullptr);

  EXPECT_EQ(s2->value.ToUint64(), 55u);
  EXPECT_EQ(s1->value.ToUint64(), 99u);
}

TEST(SimCh10b, NBAWidthTruncation) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] narrow;\n"
      "  initial begin\n"
      "    narrow <= 32'hABCD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("narrow");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

TEST(SimCh10b, NBAArithmeticExpression) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a;\n"
      "  logic [31:0] b;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    a = 15;\n"
      "    b = 27;\n"
      "    result <= a + b;\n"
      "  end\n"
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

TEST(SimCh10b, NBABitwiseOperators) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  logic [7:0] r_and;\n"
      "  logic [7:0] r_or;\n"
      "  logic [7:0] r_xor;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    b = 8'h3C;\n"
      "    r_and <= a & b;\n"
      "    r_or  <= a | b;\n"
      "    r_xor <= a ^ b;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design,
                   {{"r_and", 0x30u}, {"r_or", 0xFCu}, {"r_xor", 0xCCu}});
}

TEST(SimCh10b, NBAShiftOperators) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] val;\n"
      "  logic [7:0] r_shl;\n"
      "  logic [7:0] r_shr;\n"
      "  initial begin\n"
      "    val = 8'h0F;\n"
      "    r_shl <= val << 2;\n"
      "    r_shr <= val >> 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* r_shl = f.ctx.FindVariable("r_shl");
  auto* r_shr = f.ctx.FindVariable("r_shr");
  ASSERT_NE(r_shl, nullptr);
  ASSERT_NE(r_shr, nullptr);

  EXPECT_EQ(r_shl->value.ToUint64(), 0x3Cu);

  EXPECT_EQ(r_shr->value.ToUint64(), 0x07u);
}

TEST(SimCh10b, NBAComparisonResult) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a;\n"
      "  logic [31:0] b;\n"
      "  logic r_eq;\n"
      "  logic r_lt;\n"
      "  logic r_gt;\n"
      "  initial begin\n"
      "    a = 10;\n"
      "    b = 20;\n"
      "    r_eq <= (a == b);\n"
      "    r_lt <= (a < b);\n"
      "    r_gt <= (a > b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* r_eq = f.ctx.FindVariable("r_eq");
  auto* r_lt = f.ctx.FindVariable("r_lt");
  auto* r_gt = f.ctx.FindVariable("r_gt");
  ASSERT_NE(r_eq, nullptr);
  ASSERT_NE(r_lt, nullptr);
  ASSERT_NE(r_gt, nullptr);
  EXPECT_EQ(r_eq->value.ToUint64(), 0u);
  EXPECT_EQ(r_lt->value.ToUint64(), 1u);
  EXPECT_EQ(r_gt->value.ToUint64(), 0u);
}

TEST(SimCh10b, MixedBlockingAndNBA) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a;\n"
      "  logic [31:0] b;\n"
      "  initial begin\n"
      "    a = 5;\n"
      "    b <= a + 1;\n"
      "    a = 10;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 10u}, {"b", 6u}});
}

TEST(SimCh10b, MultipleNBAsInSequence) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a;\n"
      "  logic [31:0] b;\n"
      "  logic [31:0] c;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b <= a;\n"
      "    a = 2;\n"
      "    c <= a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* b = f.ctx.FindVariable("b");
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(b, nullptr);
  ASSERT_NE(c, nullptr);

  EXPECT_EQ(b->value.ToUint64(), 1u);
  EXPECT_EQ(c->value.ToUint64(), 2u);
}

TEST(SimCh10b, NBARegisterFilePattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] regfile [0:3];\n"
      "  initial begin\n"
      "    regfile[0] <= 100;\n"
      "    regfile[1] <= 200;\n"
      "    regfile[2] <= 300;\n"
      "    regfile[3] <= 400;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* r0 = f.ctx.FindVariable("regfile[0]");
  auto* r1 = f.ctx.FindVariable("regfile[1]");
  auto* r2 = f.ctx.FindVariable("regfile[2]");
  auto* r3 = f.ctx.FindVariable("regfile[3]");
  ASSERT_NE(r0, nullptr);
  ASSERT_NE(r1, nullptr);
  ASSERT_NE(r2, nullptr);
  ASSERT_NE(r3, nullptr);
  EXPECT_EQ(r0->value.ToUint64(), 100u);
  EXPECT_EQ(r1->value.ToUint64(), 200u);
  EXPECT_EQ(r2->value.ToUint64(), 300u);
  EXPECT_EQ(r3->value.ToUint64(), 400u);
}

TEST(SimCh10b, NBAWidthAndToUint64) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] nibble;\n"
      "  logic [15:0] half;\n"
      "  logic [31:0] word;\n"
      "  initial begin\n"
      "    nibble <= 4'hA;\n"
      "    half   <= 16'hBEEF;\n"
      "    word   <= 32'hDEADCAFE;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* nibble = f.ctx.FindVariable("nibble");
  auto* half = f.ctx.FindVariable("half");
  auto* word = f.ctx.FindVariable("word");
  ASSERT_NE(nibble, nullptr);
  ASSERT_NE(half, nullptr);
  ASSERT_NE(word, nullptr);
  EXPECT_EQ(nibble->value.width, 4u);
  EXPECT_EQ(nibble->value.ToUint64(), 0xAu);
  EXPECT_EQ(half->value.width, 16u);
  EXPECT_EQ(half->value.ToUint64(), 0xBEEFu);
  EXPECT_EQ(word->value.width, 32u);
  EXPECT_EQ(word->value.ToUint64(), 0xDEADCAFEu);
}

TEST(SimCh10b, NBACaseDefaultBranch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] sel;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    sel = 99;\n"
      "    case (sel)\n"
      "      0: result <= 10;\n"
      "      1: result <= 20;\n"
      "      default: result <= 77;\n"
      "    endcase\n"
      "  end\n"
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

TEST(SimCh10b, NBABitwiseNot) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    result <= ~a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

TEST(SimCh10b, NBAReplicationRHS) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    result <= {4{2'b10}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xAAu);
}

}
TEST(NonblockingAssignment, VarLvalueNonblocking) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x <= 8'h99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x99u);
}
