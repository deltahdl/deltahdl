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
