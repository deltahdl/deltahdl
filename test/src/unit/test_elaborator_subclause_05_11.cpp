#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

// §5.11 — braces nest once per dimension, which C does not require. What
// rejects the flat list is the §10.9.1 element count: the outer dimension [1:2]
// takes two elements and the flat list offers six. §5.11 states no report of
// its own, opening instead by making an array literal an array assignment
// pattern or pattern expression with constant member expressions (§10.9.1), so
// §10.9.1 is where the rule the report enforces is stated.
TEST(ArrayLiteralElaboration, FlatLiteralForMultiDimRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int n [1:2][1:3] = '{0, 1, 2, 3, 4, 5};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "assignment pattern has 6 elements, but array dimension requires 2", 2,
      "10.9.1"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "assignment pattern has 2 elements, but array dimension requires 3", 2,
      "10.9.1"));
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

// §5.11 has a replication operate within one dimension, so the elements it
// supplies, its multiplier times its items, are counted against that dimension
// under the §10.9.1 rule as any positional list is. Two elements for three were
// let through, every replication excused from the count.
TEST(ArrayLiteralElaboration, ReplicationSupplyingTooFewElementsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int n [1:3] = '{2{4}};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "assignment pattern has 2 elements, but array dimension requires 3", 2,
      "10.9.1"));
}

// §5.11's own example: three copies of two items fill a dimension of six,
// which a count of the multiplier alone would reject.
TEST(ArrayLiteralElaboration,
     ReplicationOfSeveralItemsFillingDimensionAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  int n [1:2][1:6] = '{2{'{3{4, 5}}}};\n"
             "endmodule\n"));
}

// A multiplier naming a parameter supplies as many elements as its value, so a
// replication of three under a parameter of 3 fills a dimension of three.
TEST(ArrayLiteralElaboration, ReplicationByParameterFillingDimensionAccepted) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  parameter int N = 3;\n"
             "  int n [1:3] = '{N{4}};\n"
             "endmodule\n"));
}

// The element count holds for a pattern in a procedural assignment as for one
// at a module-level declaration, which alone was checked.
TEST(ArrayLiteralElaboration, WrongElementCountInProceduralAssignmentRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int a [0:2];\n"
      "  initial a = '{1, 2};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "assignment pattern has 2 elements, but array dimension requires 3", 3,
      "10.9.1"));
}

// The element count holds for an array whose dimension comes from its typedef,
// which the declaration takes before its pattern is checked.
TEST(ArrayLiteralElaboration, WrongElementCountForTypedefArrayRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  typedef int i3_t [0:2];\n"
      "  i3_t ints = '{1, 2};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "assignment pattern has 2 elements, but array dimension requires 3", 3,
      "10.9.1"));
}

// §5.11 has an array literal take its type from a prefix or from an
// assignment-like context, §10.8 lists those contexts and allows no other, and
// §10.9 gives a pattern without a prefix no type of its own. A system task's
// argument and an operator's operand are no such context. Both were accepted.
TEST(ArrayLiteralElaboration,
     UntypedPatternOutsideAssignmentLikeContextRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial begin\n"
      "    $display(\"%p\", '{1, 2});\n"
      "    x = '{1, 2} + 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kMessage =
      "assignment pattern without a type prefix outside an assignment-like "
      "context";
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 4, "10.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, 5, "10.9"));
}

// The assignment-like contexts of §10.8 type a pattern written without a
// prefix: a continuous and a procedural assignment, a typed parameter, a port
// connection, a subroutine argument, a return, the parenthesized and
// conditional forms of a right-hand value, a nondefault pattern item, and a
// static cast.
TEST(ArrayLiteralElaboration,
     UntypedPatternInEachAssignmentLikeContextAccepted) {
  EXPECT_TRUE(
      ElabOk("typedef int pair_t [0:1];\n"
             "module sub(input pair_t p);\n"
             "endmodule\n"
             "module t;\n"
             "  parameter pair_t P = '{1, 2};\n"
             "  pair_t w, v, u;\n"
             "  pair_t nested [0:1];\n"
             "  bit c;\n"
             "  assign w = '{3, 4};\n"
             "  function automatic pair_t f(pair_t a);\n"
             "    return '{a[1], a[0]};\n"
             "  endfunction\n"
             "  sub s(.p('{5, 6}));\n"
             "  initial begin\n"
             "    v = '{7, 8};\n"
             "    u = f('{9, 10});\n"
             "    v = ('{1, 1});\n"
             "    v = c ? '{2, 2} : '{3, 3};\n"
             "    nested = '{'{4, 4}, '{5, 5}};\n"
             "    v = pair_t'('{6, 6});\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
