#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>
#include <vector>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_queue.h"
#include "lexer/token.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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
  EXPECT_EQ(f.ctx.FindVariable("y")->value.ToUint64(), 300u);
}

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

TEST(ArrayReduction, StringKeyedAssociativeArrayReductionSumIntegration) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  int y;\n"
      "  initial begin\n"
      "    aa[\"a\"] = 5;\n"
      "    aa[\"b\"] = 7;\n"
      "    aa[\"c\"] = 9;\n"
      "    y = aa.sum;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.FindVariable("y")->value.ToUint64(), 21u);
}

TEST(ArrayReductionSim, NestedReductionOverTheRowsOfA2DArray) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] m [2][2] = '{ '{5, 10}, '{15, 20} };\n"
      "  int y, p;\n"
      "  initial begin\n"
      "    y = m.sum with (item.sum with (item));\n"
      "    p = m.sum with (int'(item[0]) * 100 + item.product with "
      "(int'(item)));\n"
      "    $display(\"%0d %0d\", y, p);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "50 2350\n");
}

TEST(ArrayReductionSim, TheIteratorReadsWithTheElementTypesSignedness) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int q[$] = '{5, -3};\n"
      "  int d[] = '{-1, -3};\n"
      "  bit [31:0] u[$] = '{5, -3};\n"
      "  int m [2][2] = '{ '{-3, 5}, '{-1, 2} };\n"
      "  initial\n"
      "    $display(\"%0d %0d %0d %0d\", q.sum with (int'(item < 0)),\n"
      "             d.sum with (int'(item < 0)), u.sum with (int'(item < 0)),\n"
      "             m.sum with (item.sum with (int'(item < 0))));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 2 0 2\n");
}

TEST(ArrayReductionSim, NestedReductionOverTheSubarraysOfA3DArray) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int m [1:2][2][2];\n"
      "  initial begin\n"
      "    foreach (m[i, j, k]) m[i][j][k] = (i - 1) * 4 + j * 2 + k;\n"
      "    $display(\"%0d %0d %0d\",\n"
      "             m.sum with (item.sum with (item.sum with (item))),\n"
      "             m.sum with (item[1][0]), m.sum with (item.index));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "28 8 3\n");
}

TEST(ArrayReductionSim, ReductionOnASubarraySelectFoldsItsElements) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int m2[2][3] = '{'{1, 2, 3}, '{4, 5, 6}};\n"
      "  int m3[2][2][2] = '{'{'{1, 2}, '{3, 4}}, '{'{5, 6}, '{7, 8}}};\n"
      "  int d[3:2][1:0] = '{'{1, 2}, '{3, 4}};\n"
      "  int k = 1;\n"
      "  initial\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d %0d\", m2[1].sum(), "
      "m2[k].product(),\n"
      "             m2[0].xor(), m3[1][0].sum(), m2[1].sum() with (item * 2),\n"
      "             d[3].sum(), d[2].sum());\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "15 120 0 11 30 3 7\n");
}

TEST(ArrayReductionSim, ReductionOnASubarrayOfAClassPropertyFoldsItsElements) {
  SimFixture f;
  auto out = RunCapture(
      "class H;\n"
      "  int g[2][3];\n"
      "  function int inner(); return g[1].product(); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    automatic H h = new;\n"
      "    h.g[1][0] = 7; h.g[1][1] = 5; h.g[1][2] = 13; h.g[0][2] = 2;\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d %0d\", h.g[1].sum(),\n"
      "             h.g[1].product(), h.g[1].and(), h.g[1].or(), "
      "h.g[1].xor(),\n"
      "             h.g[1].sum() with (item * 2), h.inner());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "25 455 5 15 15 50 455\n");
}

TEST(ArrayReductionSim, ReductionOverSignedElementsIsSigned) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  byte b[2] = '{-1, -2};\n"
      "  int i[2] = '{-1, -2};\n"
      "  byte q[$] = '{-1, -2};\n"
      "  int aa[int];\n"
      "  byte n[2][2] = '{'{-1, -2}, '{3, 4}};\n"
      "  int unsigned u[2] = '{32'hFFFF_FFFF, 32'hFFFF_FFFF};\n"
      "  initial begin\n"
      "    aa[1] = -1; aa[2] = -2;\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d %0d\", b.sum(), i.sum(), i.sum,\n"
      "             q.sum(), aa.sum(), n[0].sum(), u.sum());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "-3 -3 -3 -3 -3 -3 4294967294\n");
}

TEST(ArrayReductionSim, ReductionWithASignedWithExpressionIsSigned) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int q[$] = '{-1, -2};\n"
      "  int aa[int];\n"
      "  int m[2][2] = '{'{-1, -2}, '{-3, 4}};\n"
      "  initial begin\n"
      "    aa[1] = -1; aa[2] = -2;\n"
      "    $display(\"%0d %0d %0d\", q.sum() with (item),\n"
      "             aa.sum() with (item), m.sum() with (item.sum()));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "-3 -3 -2\n");
}

TEST(ArrayReductionSim, ReductionOnAnElementThatIsAnArrayFoldsItsValues) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  int r[$][2];\n"
      "  int qq[$][$];\n"
      "  int aq[int][$];\n"
      "  int af[int][2];\n"
      "  initial begin\n"
      "    r.push_back('{5, 6});\n"
      "    qq.push_back('{1, 2});\n"
      "    aq[1] = '{3, 4};\n"
      "    af[2] = '{-1, -2};\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d\", r[0].sum(), qq[0].sum(),\n"
      "             aq[1].sum(), af[2].sum(), r[0].product(),\n"
      "             qq[0].sum() with (item * 10));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "11 3 7 -3 30 30\n");
}

}  // namespace
