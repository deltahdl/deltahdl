#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(AggregateExprSim, StructEqualityReturnsOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t x, y;\n"
      "  logic eq;\n"
      "  initial begin\n"
      "    x = '{8'd1, 8'd2};\n"
      "    y = '{8'd1, 8'd2};\n"
      "    eq = (x == y);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("eq");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(AggregateExprSim, StructEqualityReturnsZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t x, y;\n"
      "  logic eq;\n"
      "  initial begin\n"
      "    x = '{8'd1, 8'd2};\n"
      "    y = '{8'd3, 8'd4};\n"
      "    eq = (x == y);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("eq");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(AggregateExprSim, StructInequalityReturnsOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t x, y;\n"
      "  logic neq;\n"
      "  initial begin\n"
      "    x = '{8'd1, 8'd2};\n"
      "    y = '{8'd3, 8'd4};\n"
      "    neq = (x != y);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("neq");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(AggregateExprSim, StructInequalityReturnsZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t x, y;\n"
      "  logic neq;\n"
      "  initial begin\n"
      "    x = '{8'd5, 8'd10};\n"
      "    y = '{8'd5, 8'd10};\n"
      "    neq = (x != y);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("neq");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(AggregateExprSim, StructCopiedInAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t x, y;\n"
      "  initial begin\n"
      "    x = '{8'd42, 8'd99};\n"
      "    y = x;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* src = f.ctx.FindVariable("x");
  auto* dst = f.ctx.FindVariable("y");
  ASSERT_NE(src, nullptr);
  ASSERT_NE(dst, nullptr);
  EXPECT_EQ(dst->value.ToUint64(), src->value.ToUint64());
}

TEST(AggregateExprSim, StructPassedToFunction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic [15:0] a; logic [15:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  int result;\n"
      "  function automatic int sum(input pair_t s);\n"
      "    return s.a + s.b;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    p = '{16'd10, 16'd20};\n"
      "    result = sum(p);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(AggregateExprSim, ArrayEqualityReturnsOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a[3];\n"
      "  int b[3];\n"
      "  logic eq;\n"
      "  initial begin\n"
      "    a[0] = 1; a[1] = 2; a[2] = 3;\n"
      "    b[0] = 1; b[1] = 2; b[2] = 3;\n"
      "    eq = (a == b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("eq");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(AggregateExprSim, ArrayEqualityReturnsZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a[3];\n"
      "  int b[3];\n"
      "  logic eq;\n"
      "  initial begin\n"
      "    a[0] = 1; a[1] = 2; a[2] = 3;\n"
      "    b[0] = 1; b[1] = 9; b[2] = 3;\n"
      "    eq = (a == b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("eq");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(AggregateExprSim, ArrayInequalityReturnsOne) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a[3];\n"
      "  int b[3];\n"
      "  logic neq;\n"
      "  initial begin\n"
      "    a[0] = 1; a[1] = 2; a[2] = 3;\n"
      "    b[0] = 1; b[1] = 9; b[2] = 3;\n"
      "    neq = (a != b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("neq");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(AggregateExprSim, ArrayInequalityReturnsZero) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a[3];\n"
      "  int b[3];\n"
      "  logic neq;\n"
      "  initial begin\n"
      "    a[0] = 5; a[1] = 10; a[2] = 15;\n"
      "    b[0] = 5; b[1] = 10; b[2] = 15;\n"
      "    neq = (a != b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("neq");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(AggregateExprSim, ArrayCopiedInAssignment) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int a[3];\n"
      "  int b[3];\n"
      "  initial begin\n"
      "    a[0] = 11; a[1] = 22; a[2] = 33;\n"
      "    b = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* dst = f.ctx.FindVariable("b[1]");
  ASSERT_NE(dst, nullptr);
  EXPECT_EQ(dst->value.ToUint64(), 22u);
}

TEST(AggregateExprSim, ArrayPassedToFunction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef int arr_t [0:1];\n"
      "  arr_t a;\n"
      "  int result;\n"
      "  function automatic int sum(input arr_t x);\n"
      "    return x[0] + x[1];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    a[0] = 7; a[1] = 8;\n"
      "    result = sum(a);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

}  // namespace
