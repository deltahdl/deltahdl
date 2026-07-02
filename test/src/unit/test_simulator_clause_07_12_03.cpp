#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "parser/ast.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

void MakeFixedArray(SimFixture& f, std::string_view name,
                    const std::vector<uint64_t>& vals, uint32_t elem_width) {
  for (size_t i = 0; i < vals.size(); ++i) {
    // SimContext keys variables by std::string_view, so the element-name
    // backing storage must outlive the map entry; persist it in the arena the
    // way the lowerer does (lowerer_var.cpp) rather than passing a local
    // std::string that dangles once the loop iteration ends.
    auto ename = std::string(name) + "[" + std::to_string(i) + "]";
    auto* stored = f.arena.Create<std::string>(std::move(ename));
    auto* var = f.ctx.CreateVariable(*stored, elem_width);
    var->value = MakeLogic4VecVal(f.arena, elem_width, vals[i]);
  }
  ArrayInfo info;
  info.lo = 0;
  info.size = static_cast<uint32_t>(vals.size());
  info.elem_width = elem_width;
  info.is_dynamic = false;
  f.ctx.RegisterArray(name, info);
}

void MakeDynArrayW(SimFixture& f, std::string_view name,
                   const std::vector<uint64_t>& vals, uint32_t elem_width) {
  auto* q = f.ctx.CreateQueue(name, elem_width);
  for (auto v : vals) {
    q->elements.push_back(MakeLogic4VecVal(f.arena, elem_width, v));
  }
  ArrayInfo info;
  info.is_dynamic = true;
  info.elem_width = elem_width;
  info.size = static_cast<uint32_t>(vals.size());
  f.ctx.RegisterArray(name, info);
}

TEST(ArrayReduction, SumAllElements) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 30, 40});
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "sum", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 100u);
}

TEST(ArrayReduction, ProductAllElements) {
  SimFixture f;
  MakeDynArray(f, "arr", {2, 3, 5});
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "product", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 30u);
}

TEST(ArrayReduction, AndAllElements) {
  SimFixture f;
  MakeDynArray(f, "arr", {0xFF, 0x0F, 0x03});
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "and", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0x03u);
}

TEST(ArrayReduction, OrAllElements) {
  SimFixture f;
  MakeDynArray(f, "arr", {0x01, 0x02, 0x04});
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "or", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0x07u);
}

TEST(ArrayReduction, XorAllElements) {
  SimFixture f;
  MakeDynArray(f, "arr", {0x0F, 0xFF, 0xF0});
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "xor", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0x00u);
}

TEST(ArrayReduction, SumFixedSizeArray) {
  SimFixture f;
  MakeFixedArray(f, "arr", {10, 20, 30}, 32);
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "sum", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 60u);
}

TEST(ArrayReduction, ProductFixedSizeArray) {
  SimFixture f;
  MakeFixedArray(f, "arr", {2, 3, 7}, 32);
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "product", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 42u);
}

TEST(ArrayReduction, AndFixedSizeArray) {
  SimFixture f;
  MakeFixedArray(f, "arr", {0xFF, 0x0F}, 8);
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "and", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0x0Fu);
}

TEST(ArrayReduction, OrFixedSizeArray) {
  SimFixture f;
  MakeFixedArray(f, "arr", {0x01, 0x02, 0x04}, 8);
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "or", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0x07u);
}

TEST(ArrayReduction, XorFixedSizeArray) {
  SimFixture f;
  MakeFixedArray(f, "arr", {0x0F, 0xFF}, 8);
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "xor", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0xF0u);
}

TEST(ArrayReduction, SumEmptyArray) {
  SimFixture f;
  MakeDynArray(f, "arr", {});
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "sum", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
}

TEST(ArrayReduction, ProductEmptyArray) {
  SimFixture f;
  MakeDynArray(f, "arr", {});
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "product", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 1u);
}

TEST(ArrayReduction, XorEmptyArray) {
  SimFixture f;
  MakeDynArray(f, "arr", {});
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "xor", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
}

TEST(ArrayReduction, OrEmptyArray) {
  SimFixture f;
  MakeDynArray(f, "arr", {});
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "or", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
}

TEST(ArrayReduction, AndEmptyArray) {
  SimFixture f;
  MakeDynArray(f, "arr", {});
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "and", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 0u);
}

TEST(ArrayReduction, SumReturnWidthMatchesElementType) {
  SimFixture f;
  MakeDynArrayW(f, "arr", {1, 2, 3}, 8);
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "sum", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.width, 8u);
  EXPECT_EQ(out.ToUint64(), 6u);
}

TEST(ArrayReduction, ProductReturnWidthMatchesElementType) {
  SimFixture f;
  MakeDynArrayW(f, "arr", {2, 3, 5}, 8);
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "product", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.width, 8u);
  EXPECT_EQ(out.ToUint64(), 30u);
}

TEST(ArrayReduction, AndReturnWidthMatchesElementType) {
  SimFixture f;
  MakeDynArrayW(f, "arr", {0xFF, 0x0F}, 8);
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "and", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.width, 8u);
}

TEST(ArrayReduction, SumSingleElement) {
  SimFixture f;
  MakeDynArray(f, "arr", {42});
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "sum", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 42u);
}

TEST(ArrayReduction, ProductSingleElement) {
  SimFixture f;
  MakeDynArray(f, "arr", {7});
  Logic4Vec out;
  bool ok = TryEvalArrayProperty("arr", "product", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 7u);
}

TEST(ArrayReduction, SumCallSyntax) {
  SimFixture f;
  MakeDynArray(f, "arr", {10, 20, 30});
  auto* call = MakeMethodCall(f.arena, "arr", "sum", {});
  Logic4Vec out;
  bool ok = TryEvalArrayMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 60u);
}

TEST(ArrayReduction, ProductCallSyntax) {
  SimFixture f;
  MakeDynArray(f, "arr", {2, 3, 5});
  auto* call = MakeMethodCall(f.arena, "arr", "product", {});
  Logic4Vec out;
  bool ok = TryEvalArrayMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 30u);
}

// §7.12.3: when a with clause is present, the result takes the width of the
// with expression, not the element width. Here the element is a single bit but
// the with expression is 32 bits wide, so summing four ones must yield a
// 32-bit 4 rather than overflowing a 1-bit result.
TEST(ArrayReduction, WithClauseResultWidthMatchesExprWidth) {
  SimFixture f;
  MakeDynArrayW(f, "bits", {1, 1, 1, 1}, 1);

  auto* with_expr = MakeBinary(f.arena, TokenKind::kPlus,
                               MakeId(f.arena, "item"), MakeInt(f.arena, 0));
  auto* call = MakeMethodCall(f.arena, "bits", "sum", {});
  call->with_expr = with_expr;
  Logic4Vec out;
  bool ok = TryEvalArrayMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.width, 32u);
  EXPECT_EQ(out.ToUint64(), 4u);
}

TEST(ArrayReduction, SumIntegration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{8'd10, 8'd20, 8'd30};\n"
      "  logic [31:0] total;\n"
      "  initial total = arr.sum();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("total")->value.ToUint64(), 60u);
}

// §10.10/§7.12.3 end-to-end: a dynamic array initialized with an unsized-
// literal `{...}` concatenation (as opposed to a fixed array with an `'{...}`
// assignment pattern) must elaborate, lower into a populated queue, and reduce
// correctly. This is the exact full-pipeline seam the isolated reduction tests
// (hand-built SimContext) and the fixed-array `'{...}` Integration tests miss.
TEST(ArrayReduction, DynamicArrayConcatInitSumIntegration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte b[] = { 1, 2, 3, 4 };\n"
      "  int y;\n"
      "  initial y = b.sum;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("y")->value.ToUint64(), 10u);
}

TEST(ArrayReduction, ProductIntegration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{8'd2, 8'd3, 8'd7};\n"
      "  logic [31:0] total;\n"
      "  initial total = arr.product();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("total")->value.ToUint64(), 42u);
}

TEST(ArrayReduction, AndIntegration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:1] = '{8'hFF, 8'h0F};\n"
      "  logic [7:0] r;\n"
      "  initial r = arr.and;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 0x0Fu);
}

TEST(ArrayReduction, OrIntegration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:2] = '{8'h01, 8'h02, 8'h04};\n"
      "  logic [7:0] r;\n"
      "  initial r = arr.or;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 0x07u);
}

TEST(ArrayReduction, XorIntegration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [0:1] = '{8'h0F, 8'hFF};\n"
      "  logic [7:0] r;\n"
      "  initial r = arr.xor;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("r")->value.ToUint64(), 0xF0u);
}

// §7.12.3 end-to-end: when a with clause is present the reduction operates on
// the per-element value produced by the with expression, not the raw element.
// Driven from real source through parse/elaborate/lower/run so the with clause
// is exercised across the whole pipeline rather than a hand-built call node.
// sum over (item + 10) of {1,2,3,4} reduces {11,12,13,14} to 50.
TEST(ArrayReduction, WithClauseValueTransformSumIntegration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte b[] = { 1, 2, 3, 4 };\n"
      "  int y;\n"
      "  initial y = b.sum with (item + 10);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("y")->value.ToUint64(), 50u);
}

// §7.12.3 end-to-end: without a with clause the result takes the array element
// type, so an 8-bit element sum that exceeds 255 wraps modulo the element
// width. This mirrors the LRM's observation that a bare sum can overflow the
// element width; the with-clause cast test below is the companion that avoids
// it. 100+100+100 = 300, and 300 modulo 256 is 44.
TEST(ArrayReduction, DefaultSumOverflowsElementWidthIntegration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte b[] = { 100, 100, 100 };\n"
      "  int y;\n"
      "  initial y = b.sum;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("y")->value.ToUint64(), 44u);
}

// §7.12.3 end-to-end: the width of the result matches the width of the with
// expression, so casting the 8-bit element to int makes the sum a 32-bit value
// that no longer overflows. This is the LRM's bit_arr.sum with (int'(item))
// width-forcing example, driven through the full pipeline. Contrast the
// bare-sum case above, which wraps at the element width.
TEST(ArrayReduction, WithClauseCastForcesResultWidthIntegration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte b[] = { 100, 100, 100 };\n"
      "  int y;\n"
      "  initial y = b.sum with (int'(item));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  // Reducing 32-bit values does not overflow: 100+100+100 = 300.
  EXPECT_EQ(f.ctx.FindVariable("y")->value.ToUint64(), 300u);
}

// §7.12.3 end-to-end: product reduces the with-expression values, not the raw
// elements. Driven from source so the with clause is exercised through the full
// pipeline. product over (item + 1) of {2,3,5} reduces {3,4,6} to 72 (vs. the
// bare product 30), confirming the with values are what get multiplied.
TEST(ArrayReduction, WithClauseValueTransformProductIntegration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte b[] = { 2, 3, 5 };\n"
      "  int y;\n"
      "  initial y = b.product with (item + 1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("y")->value.ToUint64(), 72u);
}

// §7.12.3 end-to-end: and() reduces the with-expression values. ANDing
// (item + 1) of {6,3} reduces 7 & 4 to 4 (vs. the bare and 6 & 3 = 2).
TEST(ArrayReduction, WithClauseValueTransformAndIntegration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte b[] = { 6, 3 };\n"
      "  int y;\n"
      "  initial y = b.and with (item + 1);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("y")->value.ToUint64(), 4u);
}

// §7.12.3 end-to-end: or() reduces the with-expression values. ORing
// (item + 8) of {1,2,4} reduces 9 | 10 | 12 to 15 (vs. the bare or 1|2|4 = 7).
TEST(ArrayReduction, WithClauseValueTransformOrIntegration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte b[] = { 1, 2, 4 };\n"
      "  int y;\n"
      "  initial y = b.or with (item + 8);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("y")->value.ToUint64(), 15u);
}

// §7.12.3 end-to-end: xor() reduces the with-expression values. XORing
// (item + 4) of {1,2,3,4} reduces 5 ^ 6 ^ 7 ^ 8 to 12 (vs. the bare xor 4).
TEST(ArrayReduction, WithClauseValueTransformXorIntegration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte b[] = { 1, 2, 3, 4 };\n"
      "  int y;\n"
      "  initial y = b.xor with (item + 4);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("y")->value.ToUint64(), 12u);
}

// §7.12.3 end-to-end: reduction methods apply to a queue, which is an unpacked
// array of integral values just like a fixed or dynamic array. Built from real
// queue source (§7.10 dependency) and driven through the full pipeline: summing
// {10,20,30,40} yields 100.
TEST(ArrayReduction, QueueReductionSumIntegration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$] = '{10, 20, 30, 40};\n"
      "  int y;\n"
      "  initial y = q.sum;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("y")->value.ToUint64(), 100u);
}

// §7.12.3 end-to-end: a with clause on a queue reduction reduces the yielded
// values. Over {1,2,3} the expression item+10 yields {11,12,13}, summing to 36.
TEST(ArrayReduction, QueueReductionWithClauseIntegration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$] = '{1, 2, 3};\n"
      "  int y;\n"
      "  initial y = q.sum with (item + 10);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("y")->value.ToUint64(), 36u);
}

// §7.12.3 end-to-end: the with clause also applies when the reduction is written
// as a parenthesized method call (arr.sum() with (e)), a distinct parse from the
// bare member-access form above. Both route to the same value-reducing fold;
// over {1,2,3,4} the expression item+10 yields {11,12,13,14}, summing to 50.
TEST(ArrayReduction, CallFormWithClauseSumIntegration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte b[] = { 1, 2, 3, 4 };\n"
      "  int y;\n"
      "  initial y = b.sum() with (item + 10);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("y")->value.ToUint64(), 50u);
}

// §7.12.3 end-to-end: reduction methods apply to an associative array, another
// unpacked array of integral values. Built from real associative-array source
// (§7.8 dependency), populated by element writes, and driven through the full
// pipeline: summing the stored values {10,20,30} yields 60.
TEST(ArrayReduction, AssociativeArrayReductionSumIntegration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  int y;\n"
      "  initial begin\n"
      "    aa[1] = 10;\n"
      "    aa[5] = 20;\n"
      "    aa[9] = 30;\n"
      "    y = aa.sum;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("y")->value.ToUint64(), 60u);
}

// §7.12.3 end-to-end: a with clause on an associative-array reduction reduces
// the yielded values. Over stored {10,20,30} the expression item+1 yields
// {11,21,31}, summing to 63.
TEST(ArrayReduction, AssociativeArrayReductionWithClauseIntegration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int aa[int];\n"
      "  int y;\n"
      "  initial begin\n"
      "    aa[1] = 10;\n"
      "    aa[5] = 20;\n"
      "    aa[9] = 30;\n"
      "    y = aa.sum with (item + 1);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("y")->value.ToUint64(), 63u);
}

}  // namespace
