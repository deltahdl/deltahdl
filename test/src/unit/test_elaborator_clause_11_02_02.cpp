// Non-LRM tests

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §11.2.2: Aggregate expressions can be compared with equality.
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

// §11.2.2: Aggregate expressions can be compared with inequality.
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

// §11.2.2: Aggregate expressions can be passed as subroutine arguments.
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

// §11.2.2: Unpacked array equality comparison.
TEST(AggregateExpr, ArrayEqualityComparison) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int a [4];\n"
      "  int b [4];\n"
      "  logic eq;\n"
      "  initial eq = (a == b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §11.2.2: Unpacked struct and array constructors can be aggregate expressions.
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

// §11.2.2: Aggregate comparison of non-equivalent types shall be an error.
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
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
