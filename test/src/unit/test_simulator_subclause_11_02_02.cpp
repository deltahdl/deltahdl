#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(AggregateExprSim, StructEqualityReturnsOne) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "eq");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(AggregateExprSim, StructEqualityReturnsZero) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "eq");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(AggregateExprSim, StructInequalityReturnsOne) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "neq");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(AggregateExprSim, StructInequalityReturnsZero) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "neq");
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
  auto* var = RunAndFindVar(
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
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(AggregateExprSim, ArrayEqualityReturnsOne) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "eq");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(AggregateExprSim, ArrayEqualityReturnsZero) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "eq");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(AggregateExprSim, ArrayInequalityReturnsOne) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "neq");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(AggregateExprSim, ArrayInequalityReturnsZero) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "neq");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0u);
}

TEST(AggregateExprSim, ArrayCopiedInAssignment) {
  SimFixture f;
  auto* dst = RunAndFindVar(
      "module t;\n"
      "  int a[3];\n"
      "  int b[3];\n"
      "  initial begin\n"
      "    a[0] = 11; a[1] = 22; a[2] = 33;\n"
      "    b = a;\n"
      "  end\n"
      "endmodule\n",
      f, "b[1]");
  ASSERT_NE(dst, nullptr);
  EXPECT_EQ(dst->value.ToUint64(), 22u);
}

TEST(AggregateExprSim, ArrayPassedToFunction) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

// §11.2.2 with §7.5: unpacked structures compare member by member, a dynamic
// array member by the elements it holds, however each structure came to hold
// them; one differing element, or one more, makes them unequal.
TEST(AggregateEqualityRun, StructuresCompareADynamicMemberByItsElements) {
  SimFixture f;
  std::string out = RunCapture(
      "typedef struct { int a; byte data[]; } h_t;\n"
      "module t;\n"
      "  h_t x, y, w;\n"
      "  initial begin\n"
      "    x.a = 1; x.data = new[2]; x.data[0] = 5;\n"
      "    y.a = 1; y.data = new[2]; y.data[0] = 5;\n"
      "    w = y; w.data.push_back(0);\n"
      "    $display(\"%0d %0d %0d\", x == y, x != y, x == w);\n"
      "    y.data[1] = 3;\n"
      "    $display(\"%0d %0d\", x == y, x != y);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 0 0\n0 1\n");
}

// §11.2.2 with §11.4.5: the case equality operators compare the dynamic
// member by its elements too, and so does a comparison of two class
// properties holding the structure.
TEST(AggregateEqualityRun, CaseEqualityAndPropertiesCompareTheElements) {
  SimFixture f;
  std::string out = RunCapture(
      "typedef struct { int a; byte data[]; } h_t;\n"
      "class P; h_t h; endclass\n"
      "module t;\n"
      "  h_t x, y;\n"
      "  initial begin\n"
      "    static P p = new, q = new;\n"
      "    x.a = 1; x.data = new[2]; x.data[0] = 5;\n"
      "    y.a = 1; y.data = new[2]; y.data[0] = 5;\n"
      "    p.h = x;\n"
      "    q.h.a = 1; q.h.data = new[2]; q.h.data[0] = 5;\n"
      "    $display(\"%0d %0d %0d\", x === y, x !== y, p.h == q.h);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 0 1\n");
}

}  // namespace
