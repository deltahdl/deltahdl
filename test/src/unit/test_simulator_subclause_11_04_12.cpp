#include <gtest/gtest.h>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(ConcatenationSim, PartSelectOnConcatRhsFullPipeline) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  logic [3:0] a, b;\n"
                      "  logic [3:0] result;\n"
                      "  initial begin\n"
                      "    a = 4'hA;\n"
                      "    b = 4'h5;\n"
                      "    result = {a, b}[5:2];\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0x9u);
}

TEST(ConcatenationSim, BitSelectOnConcatRhsFullPipeline) {
  const char* src =
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic b7, b0, b4;\n"
      "  initial begin\n"
      "    a = 4'hA;\n"
      "    b = 4'h5;\n"
      "    b7 = {a, b}[7];\n"
      "    b0 = {a, b}[0];\n"
      "    b4 = {a, b}[4];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "b7"), 1u);
  EXPECT_EQ(RunAndGet(src, "b0"), 1u);
  EXPECT_EQ(RunAndGet(src, "b4"), 0u);
}

TEST(ConcatenationSim, LhsConcatDistributesToScalarTargets) {
  const char* src =
      "module t;\n"
      "  logic log1, log2, log3;\n"
      "  logic [2:0] r;\n"
      "  initial begin\n"
      "    {log1, log2, log3} = 3'b101;\n"
      "    r = {log1, log2, log3};\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "r"), 0b101u);
  EXPECT_EQ(RunAndGet(src, "log1"), 1u);
  EXPECT_EQ(RunAndGet(src, "log2"), 0u);
  EXPECT_EQ(RunAndGet(src, "log3"), 1u);
}

TEST(EvalOp, ConcatXZPropagation) {
  SimFixture f;

  MakeVar4(f, "ca", 4, 0b1001, 0b0101);

  auto* bv = f.ctx.CreateVariable("cb", 4);
  bv->value = MakeLogic4VecVal(f.arena, 4, 0b0101);

  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "ca"));
  concat->elements.push_back(MakeId(f.arena, "cb"));

  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);

  EXPECT_EQ(result.words[0].aval, 0x95u);
  EXPECT_EQ(result.words[0].bval, 0x50u);
}

TEST(EvalOp, ConcatWidthIsSumOfElements) {
  SimFixture f;

  auto* va = f.ctx.CreateVariable("a", 8);
  va->value = MakeLogic4VecVal(f.arena, 8, 0xAB);

  auto* vb = f.ctx.CreateVariable("b", 4);
  vb->value = MakeLogic4VecVal(f.arena, 4, 0xC);

  auto* concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "a"));
  concat->elements.push_back(MakeId(f.arena, "b"));

  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_EQ(result.width, 12u);
  EXPECT_EQ(result.ToUint64(), 0xABCu);
}

TEST(ConcatenationSim, LhsConcatInAFunctionBodyDistributesToScalarTargets) {
  const char* src =
      "module t;\n"
      "  logic log1, log2, log3;\n"
      "  function void put();\n"
      "    {log1, log2, log3} = 3'b101;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    log1 = 0; log2 = 0; log3 = 0;\n"
      "    put();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "log1"), 1u);
  EXPECT_EQ(RunAndGet(src, "log2"), 0u);
  EXPECT_EQ(RunAndGet(src, "log3"), 1u);
}

TEST(ConcatenationSim, LhsConcatInATaskBodyTakesTheCarryOut) {
  const char* src =
      "module t;\n"
      "  logic [15:0] a, b;\n"
      "  logic carry;\n"
      "  logic [15:0] acc;\n"
      "  task add();\n"
      "    {carry, acc} = a + b;\n"
      "  endtask\n"
      "  initial begin\n"
      "    a = 16'hFFFF;\n"
      "    b = 16'h0001;\n"
      "    carry = 0; acc = 16'hFFFF;\n"
      "    add();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "carry"), 1u);
  EXPECT_EQ(RunAndGet(src, "acc"), 0u);
}

TEST(ConcatenationSim, LhsConcatInAFunctionBodyReachesANestedConcatenation) {
  const char* src =
      "module t;\n"
      "  logic p, q, r;\n"
      "  function void put();\n"
      "    {p, {q, r}} = 3'b101;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    p = 0; q = 0; r = 0;\n"
      "    put();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "p"), 1u);
  EXPECT_EQ(RunAndGet(src, "q"), 0u);
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

TEST(ConcatenationSim, LhsConcatInAFunctionBodyWritesOnlyTheBitsASelectNames) {
  const char* src =
      "module t;\n"
      "  logic x;\n"
      "  logic [7:0] v;\n"
      "  function void put();\n"
      "    {x, v[3:0]} = 5'b1_1010;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    v = 8'hF0;\n"
      "    put();\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "x"), 1u);
  EXPECT_EQ(RunAndGet(src, "v"), 0xFAu);
}

TEST(ConcatenationSim, LhsConcatSelectElementWakesAnEventControlOnItsVariable) {
  SimFixture f;
  auto* woke = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic [7:0] woke;\n"
      "  initial begin\n"
      "    b = 8'hFF;\n"
      "    woke = 8'd0;\n"
      "    #1 a = 8'hF0;\n"
      "    #1 {a[3:0], b} = 12'h9AB;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(a) woke = woke + 1;\n"
      "endmodule\n",
      f, "woke");
  ASSERT_NE(woke, nullptr);
  EXPECT_EQ(woke->value.ToUint64(), 2u);
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 0xF9u);
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 0xABu);
}

TEST(ConcatenationSim,
     LhsConcatWholeVariableElementWakesAnEventControlOnItsVariable) {
  SimFixture f;
  auto* woke = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic [7:0] woke;\n"
      "  initial begin\n"
      "    b = 8'hFF;\n"
      "    woke = 8'd0;\n"
      "    #1 a = 8'hF0;\n"
      "    #1 {a, b} = 16'hF9AB;\n"
      "    #1 $finish;\n"
      "  end\n"
      "  always @(a) woke = woke + 1;\n"
      "endmodule\n",
      f, "woke");
  ASSERT_NE(woke, nullptr);
  EXPECT_EQ(woke->value.ToUint64(), 2u);
  auto* a = f.ctx.FindVariable("a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 0xF9u);
}

TEST(ConcatenationSim,
     LhsConcatElementWithOutOfBoundsBitSelectStillReservesItsBit) {
  const char* src =
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'h1A;\n"
      "    b = 8'h2B;\n"
      "    c = 8'h3C;\n"
      "    {c, a[9], b} = 17'h1AAC3;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "a"), 0x1Au);
  EXPECT_EQ(RunAndGet(src, "b"), 0xC3u);
  EXPECT_EQ(RunAndGet(src, "c"), 0xD5u);
}

TEST(ConcatenationSim,
     LhsConcatWhollyOutOfBoundsPartSelectReservesTheWidthItsIndicesName) {
  const char* src =
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'h1A;\n"
      "    b = 8'h2B;\n"
      "    c = 8'h3C;\n"
      "    {c, a[11:9], b} = 19'h6ABC3;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "a"), 0x1Au);
  EXPECT_EQ(RunAndGet(src, "b"), 0xC3u);
  EXPECT_EQ(RunAndGet(src, "c"), 0xD5u);
}

TEST(ConcatenationSim,
     LhsConcatPartiallyOutOfBoundsPartSelectWritesOnlyItsInRangeBits) {
  const char* src =
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'h1A;\n"
      "    b = 8'h2B;\n"
      "    c = 8'h3C;\n"
      "    {c, a[9:6], b} = 20'hD5AC3;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "a"), 0x9Au);
  EXPECT_EQ(RunAndGet(src, "b"), 0xC3u);
  EXPECT_EQ(RunAndGet(src, "c"), 0xD5u);
}

TEST(ConcatenationSim, LhsConcatPackedArrayElementReservesItsElementWidth) {
  const char* src =
      "module t;\n"
      "  logic [3:0][7:0] pa;\n"
      "  logic [7:0] b, c;\n"
      "  initial begin\n"
      "    pa = 32'h11223344;\n"
      "    b = 8'h2B;\n"
      "    c = 8'h3C;\n"
      "    {c, pa[1], b} = 24'hD57EC3;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "pa"), 0x11227E44u);
  EXPECT_EQ(RunAndGet(src, "b"), 0xC3u);
  EXPECT_EQ(RunAndGet(src, "c"), 0xD5u);
}

TEST(ConcatenationSim, LhsConcatZeroWidthPartSelectElementClaimsNoBits) {
  SimFixture f;
  auto* a = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  logic [3:0] w;\n"
      "  initial begin\n"
      "    a = 8'h1A;\n"
      "    b = 8'h2B;\n"
      "    c = 8'h3C;\n"
      "    w = 4'd0;\n"
      "    {c, a[3 +: w], b} = 18'h2D5C3;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 0x1Au);
  auto* c = f.ctx.FindVariable("c");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->value.ToUint64(), 0xD5u);
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->value.ToUint64(), 0xC3u);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "indexed part-select width must be a constant expression", 9, "11.5.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "zero-width part-select is not allowed", 9,
                            "11.5.1"));
}

TEST(ConcatenationSim, LhsConcatSelectElementSizesTheRhsContextByItsOwnWidth) {
  const char* src =
      "module t;\n"
      "  logic [7:0] m, n, d;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    m = 8'd200;\n"
      "    n = 8'd200;\n"
      "    d = 8'd7;\n"
      "    x = 8'hE0;\n"
      "    y = 8'h3C;\n"
      "    {x[3:0], y} = m * n / d;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "x"), 0xE1u);
  EXPECT_EQ(RunAndGet(src, "y"), 0xC0u);
}

TEST(ConcatenationSim,
     LhsConcatSelectElementWritesItsWindowWhereverTheBoundaryFalls) {
  const char* src =
      "module t;\n"
      "  logic [7:0] s, u;\n"
      "  logic [7:0] hi, lo;\n"
      "  initial begin\n"
      "    s = 8'd200;\n"
      "    u = 8'd200;\n"
      "    hi = 8'h3C;\n"
      "    lo = 8'hCB;\n"
      "    {hi, lo[5:2]} = s * u >> 4;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "lo"), 0xD3u);
  EXPECT_EQ(RunAndGet(src, "hi"), 0x0Cu);
}

TEST(ConcatenationSim,
     LhsConcatOfWholeVariablesSizesTheRhsContextTheSameEitherWay) {
  const char* src =
      "module t;\n"
      "  logic [7:0] m, n, d;\n"
      "  logic [7:0] p, q;\n"
      "  initial begin\n"
      "    m = 8'd200;\n"
      "    n = 8'd200;\n"
      "    d = 8'd7;\n"
      "    p = 8'hAA;\n"
      "    q = 8'h55;\n"
      "    {p, q} = m * n / d;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "p"), 0x16u);
  EXPECT_EQ(RunAndGet(src, "q"), 0x52u);
}

TEST(ConcatenationSim, LhsConcatZeroWidthPartSelectElementNames11_5_1) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] top, low;\n"
      "  logic [3:0] n;\n"
      "  initial begin\n"
      "    low = 8'h4D;\n"
      "    top = 8'h5E;\n"
      "    n = 4'd0;\n"
      "    {top, low[5 -: n]} = 12'h6F7;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto before_run = f.diag.Diagnostics().size();
  LowerAndRun(design, f);
  EXPECT_NE(FindDiagFrom(f, before_run, "zero-width part-select"), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "zero-width part-select is not allowed", 8,
                            "11.5.1"));
  auto* top = f.ctx.FindVariable("top");
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(top->value.ToUint64(), 0xF7u);
  auto* low = f.ctx.FindVariable("low");
  ASSERT_NE(low, nullptr);
  EXPECT_EQ(low->value.ToUint64(), 0x4Du);
}

TEST(ConcatenationSim, LhsConcatUnknownBoundPartSelectElementReportsNothing) {
  SimFixture f;
  auto* mid = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] hi, mid, lo;\n"
      "  logic [3:0] msb;\n"
      "  initial begin\n"
      "    mid = 8'h6C;\n"
      "    msb = 4'bxxxx;\n"
      "    {hi, mid[msb:0], lo} = 16'hD5C3;\n"
      "  end\n"
      "endmodule\n",
      f, "mid");
  ASSERT_NE(mid, nullptr);
  EXPECT_EQ(FindDiag(f, "zero-width part-select"), nullptr);
  EXPECT_EQ(mid->value.ToUint64(), 0x6Cu);
  auto* hi = f.ctx.FindVariable("hi");
  ASSERT_NE(hi, nullptr);
  EXPECT_EQ(hi->value.ToUint64(), 0xD5u);
}

TEST(ConcatenationSim, LhsConcatWritesAnUnpackedArrayElement) {
  const char* src =
      "module t;\n"
      "  logic [7:0] out [0:3];\n"
      "  logic [7:0] b;\n"
      "  logic [7:0] r;\n"
      "  initial begin\n"
      "    out[1] = 8'h11;\n"
      "    {out[1], b} = 16'hABCD;\n"
      "    r = out[1];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "r"), 0xABu);
  EXPECT_EQ(RunAndGet(src, "b"), 0xCDu);
}

TEST(ConcatenationSim, LhsConcatWritesAQueueElement) {
  const char* src =
      "module t;\n"
      "  logic [7:0] qu [$];\n"
      "  logic [7:0] b;\n"
      "  logic [7:0] r;\n"
      "  initial begin\n"
      "    qu.push_back(8'h11);\n"
      "    {qu[0], b} = 16'hABCD;\n"
      "    r = qu[0];\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "r"), 0xABu);
  EXPECT_EQ(RunAndGet(src, "b"), 0xCDu);
}

TEST(ConcatenationSim, LhsConcatStillWritesAPackedSelectInPlace) {
  const char* src =
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    a = 8'hF0;\n"
      "    {a[3:0], b} = 12'hABC;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "a"), 0xFAu);
  EXPECT_EQ(RunAndGet(src, "b"), 0xBCu);
}

}  // namespace
