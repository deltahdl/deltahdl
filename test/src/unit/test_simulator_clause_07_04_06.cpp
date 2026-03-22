#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_array.h"
#include "helpers_scheduler.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

TEST(ArrayOperationSimulation, EqualArrays) {
  SimFixture f;
  MakeArray4(f, "a");
  MakeArray4(f, "b");
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kEqEq,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(ArrayOperationSimulation, UnequalArrays) {
  SimFixture f;
  MakeArray4(f, "a");
  MakeArray4(f, "b");

  auto* v = f.ctx.FindVariable("b[2]");
  ASSERT_NE(v, nullptr);
  v->value = MakeLogic4VecVal(f.arena, 8, 99);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kEqEq,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(ArrayOperationSimulation, WholeArrayCopy) {
  SimFixture f;
  MakeArray4(f, "src");
  MakeArray4(f, "dst");

  auto* d0 = f.ctx.FindVariable("dst[0]");
  ASSERT_NE(d0, nullptr);
  d0->value = MakeLogic4VecVal(f.arena, 8, 99);

  auto* stmt = MakeAssign(f.arena, "dst", MakeId(f.arena, "src"));
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  for (uint32_t i = 0; i < 4; ++i) {
    auto name = "dst[" + std::to_string(i) + "]";
    auto* v = f.ctx.FindVariable(name);
    ASSERT_NE(v, nullptr);
    EXPECT_EQ(v->value.ToUint64(), (i + 1) * 10);
  }
}

TEST(ArrayOperationSimulation, PatternDistribute) {
  SimFixture f;
  f.ctx.RegisterArray("arr", {0, 3, 8, false, false, false});
  for (uint32_t i = 0; i < 3; ++i) {
    auto name = "arr[" + std::to_string(i) + "]";
    auto* s = f.arena.AllocString(name.c_str(), name.size());
    f.ctx.CreateVariable(std::string_view(s, name.size()), 8);
  }

  auto* pattern = f.arena.Create<Expr>();
  pattern->kind = ExprKind::kAssignmentPattern;
  pattern->elements = {MakeInt(f.arena, 10), MakeInt(f.arena, 20),
                       MakeInt(f.arena, 30)};

  auto* stmt = MakeAssign(f.arena, "arr", pattern);
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 10u);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 20u);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 30u);
}

TEST(ArrayOperationSimulation, InequalityEqualArrays) {
  SimFixture f;
  MakeArray4(f, "a");
  MakeArray4(f, "b");
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kBangEq,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(ArrayOperationSimulation, InequalityDifferentArrays) {
  SimFixture f;
  MakeArray4(f, "a");
  MakeArray4(f, "b");

  auto* v = f.ctx.FindVariable("b[1]");
  ASSERT_NE(v, nullptr);
  v->value = MakeLogic4VecVal(f.arena, 8, 77);
  auto result = EvalExpr(MakeBinary(f.arena, TokenKind::kBangEq,
                                    MakeId(f.arena, "a"), MakeId(f.arena, "b")),
                         f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(ArrayOperationSimulation, PackedArrayAssignFromInteger) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  int result;\n"
      "  initial begin\n"
      "    a = 8'hA5;\n"
      "    result = a;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xA5u);
}

TEST(ArrayOperationSimulation, PackedArrayArithmeticExpression) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  int result;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    result = a + 8'd3;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 13u);
}

TEST(ArrayOperationSimulation, WholeArrayCopyEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[4];\n"
      "  int b[4];\n"
      "  int result;\n"
      "  initial begin\n"
      "    a[0] = 10; a[1] = 20; a[2] = 30; a[3] = 40;\n"
      "    b = a;\n"
      "    result = b[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 30u);
}

TEST(ArrayOperationSimulation, ArrayEqualityEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[3];\n"
      "  int b[3];\n"
      "  int result;\n"
      "  initial begin\n"
      "    a[0] = 1; a[1] = 2; a[2] = 3;\n"
      "    b[0] = 1; b[1] = 2; b[2] = 3;\n"
      "    result = (a == b);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(ArrayOperationSimulation, ArrayInequalityEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[3];\n"
      "  int b[3];\n"
      "  int result;\n"
      "  initial begin\n"
      "    a[0] = 1; a[1] = 2; a[2] = 3;\n"
      "    b[0] = 1; b[1] = 99; b[2] = 3;\n"
      "    result = (a != b);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

}  // namespace
