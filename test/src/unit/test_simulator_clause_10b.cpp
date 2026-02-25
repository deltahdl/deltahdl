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

struct SimCh10bFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign* ElaborateSrc(const std::string& src, SimCh10bFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

// ---------------------------------------------------------------------------
// §10.4.2: Simple nonblocking assignment — value updates after scheduler run.
// ---------------------------------------------------------------------------
TEST(SimCh10b, SimpleNBA) {
  SimCh10bFixture f;
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

// ---------------------------------------------------------------------------
// §10.4.2: NBA does NOT take effect immediately — uses NBA region scheduling.
// The RHS is sampled in the Active region but the LHS update is deferred.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBADeferredUpdate) {
  SimCh10bFixture f;
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
  // b captures a's value before the NBA takes effect.
  EXPECT_EQ(b->value.ToUint64(), 10u);
  // a is updated in the NBA region.
  EXPECT_EQ(a->value.ToUint64(), 20u);
}

// ---------------------------------------------------------------------------
// §10.4.2: Multiple NBAs to same variable — last one wins in NBA region.
// ---------------------------------------------------------------------------
TEST(SimCh10b, MultipleNBASameVarLastWins) {
  SimCh10bFixture f;
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

// ---------------------------------------------------------------------------
// §10.4.2: NBA swap pattern — a <= b; b <= a; both capture old values.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBASwapPattern) {
  SimCh10bFixture f;
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
  // Both RHS values are sampled before either NBA takes effect.
  EXPECT_EQ(a->value.ToUint64(), 20u);
  EXPECT_EQ(b->value.ToUint64(), 10u);
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA with expression on RHS.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBAExpressionRHS) {
  SimCh10bFixture f;
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

// ---------------------------------------------------------------------------
// §10.4.2: NBA with bit-select on LHS.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBABitSelectLHS) {
  SimCh10bFixture f;
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
  // Bit 3 set: 0000_1000 = 8.
  EXPECT_EQ(var->value.ToUint64(), 8u);
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA with part-select on LHS.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBAPartSelectLHS) {
  SimCh10bFixture f;
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
  // Lower nibble set to 0xF: 0x0F = 15.
  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA with concatenation on RHS.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBAConcatenationRHS) {
  SimCh10bFixture f;
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

// ---------------------------------------------------------------------------
// §10.4.2: NBA with ternary operator on RHS.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBATernaryRHS) {
  SimCh10bFixture f;
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

// ---------------------------------------------------------------------------
// §10.4.2: NBA in always_ff block (canonical use for sequential logic).
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBAInAlwaysFF) {
  SimCh10bFixture f;
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

// ---------------------------------------------------------------------------
// §10.4.2: NBA in initial block.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBAInInitialBlock) {
  SimCh10bFixture f;
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

// ---------------------------------------------------------------------------
// §10.4.2: NBA with if-else control flow.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBAWithIfElse) {
  SimCh10bFixture f;
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
  // cond==0 → else branch for a.
  EXPECT_EQ(a->value.ToUint64(), 200u);
  // cond==1 → if branch for b.
  EXPECT_EQ(b->value.ToUint64(), 300u);
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA with case statement.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBAWithCase) {
  SimCh10bFixture f;
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

// ---------------------------------------------------------------------------
// §10.4.2: NBA in for loop.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBAInForLoop) {
  SimCh10bFixture f;
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
  // All 5 iterations read acc's blocking value (0) and schedule NBA.
  // The last NBA wins: acc <= 0 + 1 = 1.
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA with function call on RHS.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBAFunctionCallRHS) {
  SimCh10bFixture f;
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

// ---------------------------------------------------------------------------
// §10.4.2: NBA pipeline pattern — both stages use old values.
// stage2 <= stage1; stage1 <= in; (simulates a two-stage pipeline)
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBAPipelinePattern) {
  SimCh10bFixture f;
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
  // Both RHS values are sampled from old values.
  EXPECT_EQ(s2->value.ToUint64(), 55u);  // Old stage1.
  EXPECT_EQ(s1->value.ToUint64(), 99u);  // Old in_val.
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA with different widths — truncation.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBAWidthTruncation) {
  SimCh10bFixture f;
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
  // 0xABCD truncated to 8 bits = 0xCD.
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA with different widths — zero extension.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBAWidthExtension) {
  SimCh10bFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] wide;\n"
      "  initial begin\n"
      "    wide <= 8'hFF;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* var = f.ctx.FindVariable("wide");
  ASSERT_NE(var, nullptr);
  // 8'hFF zero-extended to 32 bits = 0x000000FF.
  EXPECT_EQ(var->value.ToUint64(), 0xFFu);
  EXPECT_EQ(var->value.width, 32u);
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA with arithmetic expression on RHS.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBAArithmeticExpression) {
  SimCh10bFixture f;
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

// ---------------------------------------------------------------------------
// §10.4.2: NBA with bitwise operators on RHS.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBABitwiseOperators) {
  SimCh10bFixture f;
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
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* r_and = f.ctx.FindVariable("r_and");
  auto* r_or = f.ctx.FindVariable("r_or");
  auto* r_xor = f.ctx.FindVariable("r_xor");
  ASSERT_NE(r_and, nullptr);
  ASSERT_NE(r_or, nullptr);
  ASSERT_NE(r_xor, nullptr);
  EXPECT_EQ(r_and->value.ToUint64(), 0x30u);  // 0xF0 & 0x3C = 0x30.
  EXPECT_EQ(r_or->value.ToUint64(), 0xFCu);   // 0xF0 | 0x3C = 0xFC.
  EXPECT_EQ(r_xor->value.ToUint64(), 0xCCu);  // 0xF0 ^ 0x3C = 0xCC.
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA with shift operators on RHS.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBAShiftOperators) {
  SimCh10bFixture f;
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
  // 0x0F << 2 = 0x3C (truncated to 8 bits).
  EXPECT_EQ(r_shl->value.ToUint64(), 0x3Cu);
  // 0x0F >> 1 = 0x07.
  EXPECT_EQ(r_shr->value.ToUint64(), 0x07u);
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA with comparison result on RHS.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBAComparisonResult) {
  SimCh10bFixture f;
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

// ---------------------------------------------------------------------------
// §10.4.2: Mixed blocking and nonblocking in same block — blocking first.
// ---------------------------------------------------------------------------
TEST(SimCh10b, MixedBlockingAndNBA) {
  SimCh10bFixture f;
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
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  // Blocking: a=5, then NBA samples a+1=6, then a=10.
  EXPECT_EQ(a->value.ToUint64(), 10u);
  EXPECT_EQ(b->value.ToUint64(), 6u);
}

// ---------------------------------------------------------------------------
// §10.4.2: Multiple NBAs in sequence — each captures current blocking state.
// ---------------------------------------------------------------------------
TEST(SimCh10b, MultipleNBAsInSequence) {
  SimCh10bFixture f;
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
  // b <= a when a==1, c <= a when a==2.
  EXPECT_EQ(b->value.ToUint64(), 1u);
  EXPECT_EQ(c->value.ToUint64(), 2u);
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA preserving width — result width matches LHS declaration.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBAPreservesWidth) {
  SimCh10bFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    a <= 16'hCAFE;\n"
      "    b <= 8'hBE;\n"
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
  EXPECT_EQ(a->value.width, 16u);
  EXPECT_EQ(a->value.ToUint64(), 0xCAFEu);
  EXPECT_EQ(b->value.width, 8u);
  EXPECT_EQ(b->value.ToUint64(), 0xBEu);
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA register file pattern — array elements via indexed NBA.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBARegisterFilePattern) {
  SimCh10bFixture f;
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

// ---------------------------------------------------------------------------
// §10.4.2: Verify .width and .ToUint64() on NBA results.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBAWidthAndToUint64) {
  SimCh10bFixture f;
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

// ---------------------------------------------------------------------------
// §10.4.2: NBA case default branch.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBACaseDefaultBranch) {
  SimCh10bFixture f;
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

// ---------------------------------------------------------------------------
// §10.4.2: NBA with bitwise NOT on RHS.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBABitwiseNot) {
  SimCh10bFixture f;
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
  // ~0xF0 = 0x0F (in 8 bits).
  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA with replication on RHS.
// ---------------------------------------------------------------------------
TEST(SimCh10b, NBAReplicationRHS) {
  SimCh10bFixture f;
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
  // {4{2'b10}} = 8'b10101010 = 0xAA.
  EXPECT_EQ(var->value.ToUint64(), 0xAAu);
}
