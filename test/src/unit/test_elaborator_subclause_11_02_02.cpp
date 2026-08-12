

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

// §11.2.2 states "If the two operands of a comparison operator are aggregate
// expressions, they shall be of equivalent type as defined in 6.22.2", and
// §6.22.2 is where equivalence is defined. The report names §6.22.2 because
// that is the definition the check applies, and because
// test/src/unit/test_elaborator_subclause_06_22_02.cpp and
// test/src/unit/test_elaborator_subclause_06_04.cpp already read this same
// message as §6.22.2's.
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
  const delta::Diagnostic* diag =
      FindDiag(f, "comparison of non-equivalent aggregate");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "6.22.2");
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
  // The struct type is declared at compilation-unit scope so it is visible
  // both where inner's ANSI port list names it and where m instantiates inner;
  // the aggregate s then flows through the port (§11.2.2 ¶2).
  auto* design = ElaborateSrc(
      "typedef struct { int a; int b; } pair_t;\n"
      "module inner(input pair_t p);\n"
      "endmodule\n"
      "module m;\n"
      "  pair_t s;\n"
      "  inner u(.p(s));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Inequality is the other comparison operator §11.2.2 admits, and it is held to
// the same equivalence definition in §6.22.2.
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
  const delta::Diagnostic* diag =
      FindDiag(f, "comparison of non-equivalent aggregate");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "6.22.2");
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

// Two unpacked arrays of differing size are not of equivalent type under
// §6.22.2, so comparing them breaks the requirement §11.2.2 places on aggregate
// comparison operands.
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
  const delta::Diagnostic* diag =
      FindDiag(f, "comparison of non-equivalent aggregate");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "6.22.2");
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

// The requirement holds wherever the comparison is written; a continuous
// assignment is checked against the same §6.22.2 equivalence.
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
  const delta::Diagnostic* diag =
      FindDiag(f, "comparison of non-equivalent aggregate");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "6.22.2");
}

// Array inequality, held to §6.22.2 equivalence like array equality.
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
  const delta::Diagnostic* diag =
      FindDiag(f, "comparison of non-equivalent aggregate");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "6.22.2");
}

TEST(AggregateExpr, ArrayPassedThroughPort) {
  ElabFixture f;
  // Unpacked-array type shared at compilation-unit scope so inner's ANSI port
  // list can name it; the aggregate s then flows through the port (§11.2.2 ¶2).
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
  // §11.2.2 ¶1 names a multi-element slice of an unpacked array as an
  // aggregate expression; two slices drawn from the same array type are of
  // equivalent type (§6.22.2), so comparing them is legal and elaborates
  // without a non-equivalent-aggregate error.
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

// §11.2.2 names "A multi-element slice of an unpacked array" as an aggregate
// expression, so slices of non-equivalent array types are non-equivalent
// operands and the report names the §6.22.2 definition they fail.
TEST(AggregateExpr, NonEquivalentArraySliceComparisonError) {
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
  const delta::Diagnostic* diag =
      FindDiag(f, "comparison of non-equivalent aggregate");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "6.22.2");
}

TEST(AggregateExpr, EquivalentArraySliceInequality) {
  // The inequality operator is the other comparison form §11.2.2 ¶2 admits;
  // two slices of the same array type are equivalent (§6.22.2), so an
  // inequality between them elaborates cleanly like the equality case.
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
  // Negative form: an inequality between slices of non-equivalent array types
  // is rejected just as the equality comparison is, under the same §6.22.2
  // definition of equivalent type that §11.2.2 requires the operands to meet.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef logic [7:0] arr_a [0:7];\n"
      "  typedef logic [7:0] arr_b [0:15];\n"
      "  arr_a x;\n"
      "  arr_b y;\n"
      "  logic neq;\n"
      "  initial neq = (x[0:3] != y[0:3]);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  const delta::Diagnostic* diag =
      FindDiag(f, "comparison of non-equivalent aggregate");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "6.22.2");
}

}  // namespace
