#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AggregateExpr, StructEqualityComparison) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "  pair_t x, y;\n"
      "  logic eq;\n"
      "  initial eq = (x == y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AggregateExpr, StructInequalityComparison) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "  pair_t x, y;\n"
      "  logic neq;\n"
      "  initial neq = (x != y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AggregateExpr, StructPassedToFunction) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "  pair_t p;\n"
      "  function automatic int sum(input pair_t s);\n"
      "    return s.a + s.b;\n"
      "  endfunction\n"
      "  int result;\n"
      "  initial result = sum(p);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AggregateExpr, NonEquivalentTypeComparisonError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a; } type_a;\n"
      "  typedef struct { int a; int b; } type_b;\n"
      "  type_a x;\n"
      "  type_b y;\n"
      "  logic eq;\n"
      "  initial eq = (x == y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "comparison of non-equivalent aggregate", 7,
                            "6.22.2"));
}

TEST(AggregateExpr, AssignmentPatternAsAggregate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct { int x; int y; } point_t;\n"
      "  point_t p;\n"
      "  initial p = '{1, 2};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AggregateExpr, StructCopiedInAssignment) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "  pair_t x, y;\n"
      "  initial y = x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AggregateExpr, StructPassedThroughPort) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "typedef struct { int a; int b; } pair_t;\n"
      "module inner(input var pair_t p);\n"
      "endmodule\n"
      "module m;\n"
      "  pair_t s;\n"
      "  inner u(.p(s));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AggregateExpr, NonEquivalentTypeInequalityError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a; } type_a;\n"
      "  typedef struct { int a; int b; } type_b;\n"
      "  type_a x;\n"
      "  type_b y;\n"
      "  logic neq;\n"
      "  initial neq = (x != y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "comparison of non-equivalent aggregate", 7,
                            "6.22.2"));
}

TEST(AggregateExpr, ArrayEqualityComparison) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef logic [7:0] byte_arr_t [0:3];\n"
      "  byte_arr_t a, b;\n"
      "  logic eq;\n"
      "  initial eq = (a == b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AggregateExpr, ArrayInequalityComparison) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef logic [7:0] byte_arr_t [0:3];\n"
      "  byte_arr_t a, b;\n"
      "  logic neq;\n"
      "  initial neq = (a != b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AggregateExpr, ArrayCopiedInAssignment) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef logic [7:0] byte_arr_t [0:3];\n"
      "  byte_arr_t a, b;\n"
      "  initial b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AggregateExpr, ArrayPassedToFunction) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef int arr_t [0:1];\n"
      "  arr_t a;\n"
      "  function automatic int first(input arr_t x);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  int result;\n"
      "  initial result = first(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AggregateExpr, NonEquivalentArrayTypeComparisonError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef logic [7:0] arr_a [0:3];\n"
      "  typedef logic [7:0] arr_b [0:7];\n"
      "  arr_a x;\n"
      "  arr_b y;\n"
      "  logic eq;\n"
      "  initial eq = (x == y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "comparison of non-equivalent aggregate", 7,
                            "6.22.2"));
}

TEST(AggregateExpr, EquivalentTypeComparisonInContAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a; int b; } pair_t;\n"
      "  pair_t x, y;\n"
      "  wire eq;\n"
      "  assign eq = (x == y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AggregateExpr, NonEquivalentTypeComparisonInContAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct { int a; } type_a;\n"
      "  typedef struct { int a; int b; } type_b;\n"
      "  type_a x;\n"
      "  type_b y;\n"
      "  wire eq;\n"
      "  assign eq = (x == y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "comparison of non-equivalent aggregate", 7,
                            "6.22.2"));
}

TEST(AggregateExpr, NonEquivalentArrayTypeInequalityError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef logic [7:0] arr_a [0:3];\n"
      "  typedef logic [7:0] arr_b [0:7];\n"
      "  arr_a x;\n"
      "  arr_b y;\n"
      "  logic neq;\n"
      "  initial neq = (x != y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "comparison of non-equivalent aggregate", 7,
                            "6.22.2"));
}

TEST(AggregateExpr, ArrayPassedThroughPort) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "typedef logic [7:0] arr_t [0:3];\n"
      "module inner(input arr_t a);\n"
      "endmodule\n"
      "module m;\n"
      "  arr_t s;\n"
      "  inner u(.a(s));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AggregateExpr, ArrayConstructorAsAggregate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef int arr_t [0:3];\n"
      "  arr_t a;\n"
      "  initial a = '{1, 2, 3, 4};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AggregateExpr, EquivalentArraySliceComparison) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef logic [7:0] arr_t [0:7];\n"
      "  arr_t x, y;\n"
      "  logic eq;\n"
      "  initial eq = (x[0:3] == y[0:3]);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AggregateExpr, EqualShapedSlicesOfDifferentTypedefsCompare) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef logic [7:0] arr_a [0:7];\n"
      "  typedef logic [7:0] arr_b [0:15];\n"
      "  arr_a x;\n"
      "  arr_b y;\n"
      "  logic eq;\n"
      "  initial eq = (x[0:3] == y[0:3]);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AggregateExpr, NonEquivalentArrayComparisonsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int a [4], b [8];\n"
      "  byte c [4];\n"
      "  int d [];\n"
      "  logic eq;\n"
      "  int k;\n"
      "  initial begin\n"
      "    eq = (a == b);\n"
      "    eq = (a != c);\n"
      "    eq = (a == b[0:2]);\n"
      "    eq = (a == d);\n"
      "    eq = (a == b[4:7]);\n"
      "    eq = (a == b[0 +: 4]);\n"
      "    eq = (a == b[7 -: 4]);\n"
      "    eq = (a == b[k +: 4]);\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {8u, 9u, 10u, 11u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "comparison of non-equivalent aggregate", line,
                              "6.22.2"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 4u);
}

TEST(AggregateExpr, EquivalentArraySliceInequality) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef logic [7:0] arr_t [0:7];\n"
      "  arr_t x, y;\n"
      "  logic neq;\n"
      "  initial neq = (x[0:3] != y[0:3]);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AggregateExpr, NonEquivalentArraySliceInequalityError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef logic [7:0] arr_a [0:7];\n"
      "  typedef logic [7:0] arr_b [0:15];\n"
      "  arr_a x;\n"
      "  arr_b y;\n"
      "  logic neq;\n"
      "  initial neq = (x[0:3] != y[0:4]);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "comparison of non-equivalent aggregate", 7,
                            "6.22.2"));
}

}  // namespace
