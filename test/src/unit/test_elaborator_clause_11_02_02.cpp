

#include "fixture_elaborator.h"

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

}
