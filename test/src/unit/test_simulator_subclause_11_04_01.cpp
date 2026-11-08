#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "lexer/token.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(LvalueSim, VarLvalueCompoundAdd) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int x;\n"
      "  initial begin x = 10; x += 5; end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(CompoundAssignOpEval, LtLtLtEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 1);

  auto* expr = MakeBinary(f.arena, TokenKind::kLtLtLtEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 4));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 16u);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

TEST(CompoundAssignOpEval, GtGtGtEq) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("a", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 256);

  auto* expr = MakeBinary(f.arena, TokenKind::kGtGtGtEq, MakeId(f.arena, "a"),
                          MakeInt(f.arena, 4));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 16u);
  EXPECT_EQ(var->value.ToUint64(), 16u);
}

TEST(LvalueSim, CompoundAssignWithIndexedLhs) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int arr [0:3];\n"
      "  initial begin\n"
      "    arr[0] = 0; arr[1] = 0; arr[2] = 10; arr[3] = 0;\n"
      "    arr[2] += 5;\n"
      "  end\n"
      "endmodule\n",
      f, "arr[2]");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

void RunAndCheckIndexOnce(const std::string& src, const char* target,
                          uint64_t expected) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable(target);
  auto* calls = f.ctx.FindVariable("idx_calls");
  ASSERT_NE(var, nullptr);
  ASSERT_NE(calls, nullptr);
  EXPECT_EQ(var->value.ToUint64(), expected);
  EXPECT_EQ(calls->value.ToUint64(), 1u);
}

TEST(LvalueSim, CompoundAssignEvaluatesLvalueIndexOnce) {
  RunAndCheckIndexOnce(
      "module t;\n"
      "  int arr [0:3];\n"
      "  int idx_calls;\n"
      "  function automatic int idx_fn();\n"
      "    idx_calls = idx_calls + 1;\n"
      "    return 2;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    arr[0] = 0; arr[1] = 0; arr[2] = 10; arr[3] = 0;\n"
      "    idx_calls = 0;\n"
      "    arr[idx_fn()] += 5;\n"
      "  end\n"
      "endmodule\n",
      "arr[2]", 15u);
}

TEST(LvalueSim, CompoundAssignBitSelectIndexEvaluatedOnce) {
  RunAndCheckIndexOnce(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  int idx_calls;\n"
      "  function automatic int idx_fn();\n"
      "    idx_calls = idx_calls + 1;\n"
      "    return 3;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    data = 8'b0000_0000;\n"
      "    idx_calls = 0;\n"
      "    data[idx_fn()] += 1'b1;\n"
      "  end\n"
      "endmodule\n",
      "data", 0x08u);
}

TEST(LvalueSim, CompoundAssignPartSelectBaseIndexEvaluatedOnce) {
  RunAndCheckIndexOnce(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  int idx_calls;\n"
      "  function automatic int idx_fn();\n"
      "    idx_calls = idx_calls + 1;\n"
      "    return 2;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    data = 8'b0000_0000;\n"
      "    idx_calls = 0;\n"
      "    data[idx_fn() +: 2] += 2'b11;\n"
      "  end\n"
      "endmodule\n",
      "data", 0x0Cu);
}

TEST(LvalueSim, CompoundAssignAsAnExpressionEvaluatesLvalueIndexOnce) {
  RunAndCheckIndexOnce(
      "module t;\n"
      "  int arr [0:3];\n"
      "  int idx_calls;\n"
      "  int q;\n"
      "  function automatic int idx_fn();\n"
      "    idx_calls = idx_calls + 1;\n"
      "    return 2;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    arr[0] = 0; arr[1] = 0; arr[2] = 10; arr[3] = 0;\n"
      "    idx_calls = 0;\n"
      "    q = (arr[idx_fn()] += 5);\n"
      "  end\n"
      "endmodule\n",
      "arr[2]", 15u);
}

TEST(LvalueSim, CompoundAssignAsAnExpressionEvaluatesBitSelectIndexOnce) {
  RunAndCheckIndexOnce(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  int idx_calls;\n"
      "  logic q;\n"
      "  function automatic int idx_fn();\n"
      "    idx_calls = idx_calls + 1;\n"
      "    return 3;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    data = 8'b0000_0000;\n"
      "    idx_calls = 0;\n"
      "    q = (data[idx_fn()] += 1'b1);\n"
      "  end\n"
      "endmodule\n",
      "data", 0x08u);
}

TEST(LvalueSim, CompoundAssignInAFunctionBodyWritesTheTargetOnce) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:3];\n"
      "  int idx_calls;\n"
      "  function automatic int idx_fn();\n"
      "    idx_calls = idx_calls + 1;\n"
      "    return idx_calls;\n"
      "  endfunction\n"
      "  function void bump();\n"
      "    arr[idx_fn()] += 5;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    arr[0] = 0; arr[1] = 0; arr[2] = 0; arr[3] = 0;\n"
      "    idx_calls = 0;\n"
      "    bump();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* written = f.ctx.FindVariable("arr[1]");
  auto* untouched = f.ctx.FindVariable("arr[2]");
  auto* calls = f.ctx.FindVariable("idx_calls");
  ASSERT_NE(written, nullptr);
  ASSERT_NE(untouched, nullptr);
  ASSERT_NE(calls, nullptr);
  EXPECT_EQ(written->value.ToUint64(), 5u);
  EXPECT_EQ(untouched->value.ToUint64(), 0u);
  EXPECT_EQ(calls->value.ToUint64(), 1u);
}

TEST(LvalueSim, CompoundAssignOnAPropertyInsideAMethod) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int a, c;\n"
      "  int b = 4;\n"
      "  static int s;\n"
      "  function void f();\n"
      "    a += 10;\n"
      "    this.b *= 3;\n"
      "    c = c + 10;\n"
      "    s += 7;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  C h;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.f();\n"
      "    result = h.a * 1000000 + h.b * 10000 + h.c * 100 + C::s;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* result = f.ctx.FindVariable("result");
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result->value.ToUint64(), 10121007u);
}

TEST(LvalueSim, CompoundAssignOnAHierarchicalNameAndAfterADelayInAMethod) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int a;\n"
      "  task run();\n"
      "    t.total += 1;\n"
      "    #1 a += 5;\n"
      "  endtask\n"
      "endclass\n"
      "module t;\n"
      "  int total;\n"
      "  int result;\n"
      "  C h;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.run();\n"
      "    result = h.a * 10 + total;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* result = f.ctx.FindVariable("result");
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result->value.ToUint64(), 51u);
}

TEST(LvalueSim, CompoundAssignInAFunctionBodyEvaluatesLvalueIndexOnce) {
  RunAndCheckIndexOnce(
      "module t;\n"
      "  int arr [0:3];\n"
      "  int idx_calls;\n"
      "  function automatic int idx_fn();\n"
      "    idx_calls = idx_calls + 1;\n"
      "    return 2;\n"
      "  endfunction\n"
      "  function void bump();\n"
      "    arr[idx_fn()] += 5;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    arr[0] = 0; arr[1] = 0; arr[2] = 10; arr[3] = 0;\n"
      "    idx_calls = 0;\n"
      "    bump();\n"
      "  end\n"
      "endmodule\n",
      "arr[2]", 15u);
}

TEST(LvalueSim, CompoundAssignInATaskBodyEvaluatesLvalueIndexOnce) {
  RunAndCheckIndexOnce(
      "module t;\n"
      "  int arr [0:3];\n"
      "  int idx_calls;\n"
      "  function automatic int idx_fn();\n"
      "    idx_calls = idx_calls + 1;\n"
      "    return 2;\n"
      "  endfunction\n"
      "  task bump();\n"
      "    arr[idx_fn()] += 5;\n"
      "  endtask\n"
      "  initial begin\n"
      "    arr[0] = 0; arr[1] = 0; arr[2] = 10; arr[3] = 0;\n"
      "    idx_calls = 0;\n"
      "    bump();\n"
      "  end\n"
      "endmodule\n",
      "arr[2]", 15u);
}

TEST(LvalueSim, VarLvalueCompoundAddInAFunctionBody) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int x;\n"
      "  function void bump();\n"
      "    x += 5;\n"
      "  endfunction\n"
      "  initial begin x = 10; bump(); end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(LvalueSim, CompoundAssignStructMemberLhs) {
  SimFixture f;
  auto* s = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [3:0] hi;\n"
      "    logic [3:0] lo;\n"
      "  } pair_t;\n"
      "  pair_t s;\n"
      "  initial begin\n"
      "    s.hi = 4'd2;\n"
      "    s.lo = 4'd5;\n"
      "    s.lo += 4'd3;\n"
      "  end\n"
      "endmodule\n",
      f, "s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(s->value.ToUint64(), 0x28u);
}

TEST(LvalueSim, CompoundAssignSelfReferenceDoublesValue) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int a;\n"
      "  initial begin\n"
      "    a = 5;\n"
      "    a += a;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(LvalueSim, CompoundAssignArithBitwiseShiftThroughPipeline) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int sub, mul, divr, mod;\n"
      "  int band, bor, bxor;\n"
      "  int shl, shr;\n"
      "  initial begin\n"
      "    sub = 10;  sub  -= 3;\n"
      "    mul = 6;   mul  *= 2;\n"
      "    divr = 8;  divr /= 2;\n"
      "    mod = 17;  mod  %= 5;\n"
      "    band = 'hFF; band &= 'h0F;\n"
      "    bor  = 'h01; bor  |= 'h10;\n"
      "    bxor = 'hAA; bxor ^= 'hFF;\n"
      "    shl = 1;   shl  <<= 4;\n"
      "    shr = 256; shr  >>= 4;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("sub")->value.ToUint64(), 7u);
  EXPECT_EQ(f.ctx.FindVariable("mul")->value.ToUint64(), 12u);
  EXPECT_EQ(f.ctx.FindVariable("divr")->value.ToUint64(), 4u);
  EXPECT_EQ(f.ctx.FindVariable("mod")->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("band")->value.ToUint64(), 0x0Fu);
  EXPECT_EQ(f.ctx.FindVariable("bor")->value.ToUint64(), 0x11u);
  EXPECT_EQ(f.ctx.FindVariable("bxor")->value.ToUint64(), 0x55u);
  EXPECT_EQ(f.ctx.FindVariable("shl")->value.ToUint64(), 16u);
  EXPECT_EQ(f.ctx.FindVariable("shr")->value.ToUint64(), 16u);
}

TEST(LvalueSim, ConcatSelectElementTakesOnlyTheBitsItNames) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    a = 8'hFF;\n"
      "    {a[3:0], b} = 12'h123;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64() & 0xFFu, 0xF1u);
}

TEST(LvalueSim, ConcatElementAfterASelectTakesTheBitsBelowIt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    a = 8'hFF;\n"
      "    {a[3:0], b} = 12'h123;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64() & 0xFFu, 0x23u);
}

TEST(LvalueSim, ConcatLvalueCarriesUnknownBitsToItsElements) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial {a, b} = 16'bzzzzxxxx10101010;\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "zzzzxxxx");
}

TEST(LvalueSim, ConcatLvalueReachesElementsAboveTheFirstWord) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [63:0] hi;\n"
      "  logic [63:0] lo;\n"
      "  initial {hi, lo} = 128'h1234_0000_0000_0000_0000_0000_0000_0000;\n"
      "endmodule\n",
      f, "hi");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x1234000000000000ull);
}

TEST(LvalueSim, CompoundAssignTruncatesToTheTargetWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'h2;\n"
      "    v += 8'h0F;\n"
      "  end\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.width, 4u);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(LvalueSim, CompoundAssignZeroesXzIntoATwoStateTarget) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] u;\n"
      "  bit [7:0] b;\n"
      "  initial begin\n"
      "    u = 8'b1010_x10z;\n"
      "    b = 8'h00;\n"
      "    b |= u;\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(var->value.IsKnown());
  EXPECT_EQ(var->value.ToUint64(), 0xA4u);
}

TEST(LvalueSim, CompoundAssignOfARealToAnIntegerTarget) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int i;\n"
      "  initial begin\n"
      "    i = 1;\n"
      "    i += 1.75;\n"
      "  end\n"
      "endmodule\n",
      f, "i");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(LvalueSim, CompoundAssignOfARealToAnIntegerTargetInAFunctionBody) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int i;\n"
      "  function void bump();\n"
      "    i += 1.75;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    i = 1;\n"
      "    bump();\n"
      "  end\n"
      "endmodule\n",
      f, "i");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 3u);
}

TEST(LvalueSim, CompoundAssignExpressionYieldsTheTargetsDataType) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] a;\n"
      "  int b;\n"
      "  initial begin\n"
      "    a = 4'hF;\n"
      "    b = (a += 1);\n"
      "  end\n"
      "endmodule\n",
      f, "b");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(LvalueSim, CompoundAssignExpressionWakesAnEventControlOnItsTarget) {
  SimFixture f;
  const std::string kSrc =
      "module t;\n"
      "  int x;\n"
      "  int y;\n"
      "  int hits;\n"
      "  always @(x) hits = hits + 1;\n"
      "  initial begin\n"
      "    #1 y = (x += 3);\n"
      "    #1 y = (x += 0);\n"
      "    #1 y = (x += 5);\n"
      "    #1 y = (x += 4);\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n";
  auto* hits = RunAndFindVar(kSrc, f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 3u);

  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 12u);

  auto* x = f.ctx.FindVariable("x");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 12u);
}

TEST(CompoundAssignSim, RightOperandTakesTheAssignmentsWidth) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  logic [8:0] s = 0, t = 0, v = 9'h100;\n"
                       "  logic [7:0] x = 255, y = 1;\n"
                       "  logic [8:0] e;\n"
                       "  initial begin\n"
                       "    s += x + y;\n"
                       "    e = (t += x + y);\n"
                       "    v >>= y + y;\n"
                       "    $display(\"%0d %0d %0d %h\", s, t, e, v);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "256 256 256 040\n");
}

}  // namespace
