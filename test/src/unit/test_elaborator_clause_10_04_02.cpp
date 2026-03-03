// §10.4.2: Nonblocking procedural assignments

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

  // NBA update deferred, but scheduler drains NBA after Active,
  // so after Run() completes the NBA has been applied.
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // x was read as 0 (from X init), then NBA applied 42.
  // The blocking assign `x = x` reads 0 and writes 0.
  // Then NBA applies 42. Final value: 42.
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

// ---------------------------------------------------------------------------
// §10.4.2: Simple nonblocking assignment — value updates after scheduler run.
// ---------------------------------------------------------------------------
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

// ---------------------------------------------------------------------------
// §10.4.2: NBA does NOT take effect immediately — uses NBA region scheduling.
// The RHS is sampled in the Active region but the LHS update is deferred.
// ---------------------------------------------------------------------------
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
  // b captures a's value before the NBA takes effect.
  EXPECT_EQ(b->value.ToUint64(), 10u);
  // a is updated in the NBA region.
  EXPECT_EQ(a->value.ToUint64(), 20u);
}

// ---------------------------------------------------------------------------
// §10.4.2: Multiple NBAs to same variable — last one wins in NBA region.
// ---------------------------------------------------------------------------
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

// ---------------------------------------------------------------------------
// §10.4.2: NBA swap pattern — a <= b; b <= a; both capture old values.
// ---------------------------------------------------------------------------
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
  // Both RHS values are sampled before either NBA takes effect.
  EXPECT_EQ(a->value.ToUint64(), 20u);
  EXPECT_EQ(b->value.ToUint64(), 10u);
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA with expression on RHS.
// ---------------------------------------------------------------------------
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

// ---------------------------------------------------------------------------
// §10.4.2: NBA with bit-select on LHS.
// ---------------------------------------------------------------------------
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
  // Bit 3 set: 0000_1000 = 8.
  EXPECT_EQ(var->value.ToUint64(), 8u);
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA with part-select on LHS.
// ---------------------------------------------------------------------------
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
  // Lower nibble set to 0xF: 0x0F = 15.
  EXPECT_EQ(var->value.ToUint64(), 0x0Fu);
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA with concatenation on RHS.
// ---------------------------------------------------------------------------
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

// ---------------------------------------------------------------------------
// §10.4.2: NBA with ternary operator on RHS.
// ---------------------------------------------------------------------------
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

// ---------------------------------------------------------------------------
// §10.4.2: NBA in always_ff block (canonical use for sequential logic).
// ---------------------------------------------------------------------------
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

// ---------------------------------------------------------------------------
// §10.4.2: NBA in initial block.
// ---------------------------------------------------------------------------
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

// ---------------------------------------------------------------------------
// §10.4.2: NBA with if-else control flow.
// ---------------------------------------------------------------------------
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
  // cond==0 → else branch for a.
  EXPECT_EQ(a->value.ToUint64(), 200u);
  // cond==1 → if branch for b.
  EXPECT_EQ(b->value.ToUint64(), 300u);
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA with case statement.
// ---------------------------------------------------------------------------
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

// ---------------------------------------------------------------------------
// §10.4.2: NBA in for loop.
// ---------------------------------------------------------------------------
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
  // All 5 iterations read acc's blocking value (0) and schedule NBA.
  // The last NBA wins: acc <= 0 + 1 = 1.
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA with function call on RHS.
// ---------------------------------------------------------------------------
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

// ---------------------------------------------------------------------------
// §10.4.2: NBA pipeline pattern — both stages use old values.
// stage2 <= stage1; stage1 <= in; (simulates a two-stage pipeline)
// ---------------------------------------------------------------------------
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
  // Both RHS values are sampled from old values.
  EXPECT_EQ(s2->value.ToUint64(), 55u);  // Old stage1.
  EXPECT_EQ(s1->value.ToUint64(), 99u);  // Old in_val.
}

// ---------------------------------------------------------------------------
// §10.4.2: NBA with different widths — truncation.
// ---------------------------------------------------------------------------
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
  // 0xABCD truncated to 8 bits = 0xCD.
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

}  // namespace
