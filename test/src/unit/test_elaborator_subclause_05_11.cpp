#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §5.11 — an array literal whose element count matches the array dimension
// elaborates.
TEST(ArrayLiteralElaboration, MatchingElementCountElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int n [1:3];\n"
             "  initial n = '{0, 1, 2};\n"
             "endmodule\n"));
}

// §5.11 — "The nesting of braces shall follow the number of dimensions, unlike
// in C." What rejects the flat list is the §10.9.1 element count: the outer
// dimension [1:2] takes two elements and the flat list offers six. §5.11 states
// no report of its own, opening instead with "Array literals are array
// assignment patterns or pattern expressions with constant member expressions
// (see 10.9.1)", so §10.9.1 is where the rule the report enforces is stated.
TEST(ArrayLiteralElaboration, FlatLiteralForMultiDimRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int n [1:2][1:3] = '{0, 1, 2, 3, 4, 5};\n"
      "endmodule\n",
      f);
  const Diagnostic* diag = FindDiag(
      f, "assignment pattern has 6 elements, but array dimension requires 2");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "10.9.1");
}

// §5.11 — an array literal whose element count does not match the dimension is
// rejected, under the same §10.9.1 rule.
TEST(ArrayLiteralElaboration, WrongElementCountRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int n [1:3] = '{0, 1};\n"
      "endmodule\n",
      f);
  const Diagnostic* diag = FindDiag(
      f, "assignment pattern has 2 elements, but array dimension requires 3");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "10.9.1");
}

// §5.11 — a replication operator sets values within one dimension; the inner
// brace pair is removed, so the replicated value fills the dimension.
TEST(ArrayLiteralElaboration, ReplicationFillsDimension) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int n [1:3];\n"
             "  initial n = '{3{4}};\n"
             "endmodule\n"));
}

// §5.11 — an array literal's type may be explicitly indicated with a prefix.
TEST(ArrayLiteralElaboration, TypePrefixedArrayLiteralElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef int triple [1:3];\n"
             "  triple b = triple'{0, 1, 2};\n"
             "endmodule\n"));
}

// §5.11 — an array literal's type may instead be indicated implicitly by an
// assignment-like context (see §10.8).
TEST(ArrayLiteralElaboration, AssignmentContextProvidesType) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef int triple [1:3];\n"
             "  triple b = '{0, 1, 2};\n"
             "endmodule\n"));
}

// §5.11 — an array literal can use an index as a key together with a default
// key value.
TEST(ArrayLiteralElaboration, IndexKeyWithDefaultElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef int triple [1:3];\n"
             "  triple b = '{1:1, default:0};\n"
             "endmodule\n"));
}

}  // namespace
