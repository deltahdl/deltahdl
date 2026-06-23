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

TEST(ArrayReduction, SumWithClauseTransformsValues) {
  SimFixture f;
  MakeDynArrayW(f, "b", {1, 2, 3, 4}, 8);

  auto* with_expr = MakeBinary(f.arena, TokenKind::kPlus,
                               MakeId(f.arena, "item"), MakeInt(f.arena, 10));
  auto* call = MakeMethodCall(f.arena, "b", "sum", {});
  call->with_expr = with_expr;
  Logic4Vec out;
  bool ok = TryEvalArrayMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 50u);
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

TEST(ArrayReduction, XorWithClauseTransformsValues) {
  SimFixture f;
  MakeDynArrayW(f, "b", {1, 2, 3, 4}, 8);

  auto* with_expr = MakeBinary(f.arena, TokenKind::kPlus,
                               MakeId(f.arena, "item"), MakeInt(f.arena, 4));
  auto* call = MakeMethodCall(f.arena, "b", "xor", {});
  call->with_expr = with_expr;
  Logic4Vec out;
  bool ok = TryEvalArrayMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 12u);
}

// §7.12.3: the with expression supplies the values reduced by product().
// Multiplying (item+1) over {1,2,3,4} reduces {2,3,4,5} to 120.
TEST(ArrayReduction, ProductWithClauseTransformsValues) {
  SimFixture f;
  MakeDynArrayW(f, "b", {1, 2, 3, 4}, 8);

  auto* with_expr = MakeBinary(f.arena, TokenKind::kPlus,
                               MakeId(f.arena, "item"), MakeInt(f.arena, 1));
  auto* call = MakeMethodCall(f.arena, "b", "product", {});
  call->with_expr = with_expr;
  Logic4Vec out;
  bool ok = TryEvalArrayMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 120u);
}

// §7.12.3: the with expression supplies the values reduced by and().
// ANDing (item+1) over {6,3} reduces 7 & 4 to 4.
TEST(ArrayReduction, AndWithClauseTransformsValues) {
  SimFixture f;
  MakeDynArrayW(f, "b", {6, 3}, 8);

  auto* with_expr = MakeBinary(f.arena, TokenKind::kPlus,
                               MakeId(f.arena, "item"), MakeInt(f.arena, 1));
  auto* call = MakeMethodCall(f.arena, "b", "and", {});
  call->with_expr = with_expr;
  Logic4Vec out;
  bool ok = TryEvalArrayMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 4u);
}

// §7.12.3: the with expression supplies the values reduced by or().
// ORing (item+8) over {1,2,4} reduces 9 | 10 | 12 to 15.
TEST(ArrayReduction, OrWithClauseTransformsValues) {
  SimFixture f;
  MakeDynArrayW(f, "b", {1, 2, 4}, 8);

  auto* with_expr = MakeBinary(f.arena, TokenKind::kPlus,
                               MakeId(f.arena, "item"), MakeInt(f.arena, 8));
  auto* call = MakeMethodCall(f.arena, "b", "or", {});
  call->with_expr = with_expr;
  Logic4Vec out;
  bool ok = TryEvalArrayMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 15u);
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

}  // namespace
