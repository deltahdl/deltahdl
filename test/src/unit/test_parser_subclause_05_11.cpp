#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §5.11 — an array literal is an array assignment pattern; it parses to an
// assignment-pattern expression with one element per first-dimension entry.
TEST(ArrayLiteralParsing, ArrayLiteralExprKind) {
  auto r = Parse(
      "module m;\n"
      "  int n [1:3];\n"
      "  initial n = '{0, 1, 2};\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(rhs->elements.size(), 3u);
}

// §5.11 — the nesting of braces follows the number of dimensions; a two-element
// list for a 2-D array nests one assignment pattern per row.
TEST(ArrayLiteralParsing, NestedBracesFollowDimensions) {
  auto r = Parse(
      "module m;\n"
      "  int n [1:2][1:3];\n"
      "  initial n = '{'{0, 1, 2}, '{3, 4, 5}};\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kAssignmentPattern);
  ASSERT_EQ(rhs->elements.size(), 2u);
  EXPECT_EQ(rhs->elements[0]->kind, ExprKind::kAssignmentPattern);
  EXPECT_EQ(rhs->elements[1]->kind, ExprKind::kAssignmentPattern);
}

// §5.11 — the replication operator is allowed inside an array literal.
TEST(ArrayLiteralParsing, ReplicationParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int n [1:3];\n"
              "  initial n = '{3{4}};\n"
              "endmodule\n"));
}

// §5.11 — replication operators may themselves be nested within an array
// literal (the inner brace pair belongs to the inner replication).
TEST(ArrayLiteralParsing, NestedReplicationParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int n [1:2][1:6];\n"
              "  initial n = '{2{'{3{4, 5}}}};\n"
              "endmodule\n"));
}

// §5.11 — an array literal's type may be explicitly indicated with a prefix.
TEST(ArrayLiteralParsing, TypePrefixedArrayLiteralParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef int triple [1:3];\n"
              "  triple b = triple'{0, 1, 2};\n"
              "endmodule\n"));
}

// §5.11 — an array literal may use an index as a key together with a default
// key value.
TEST(ArrayLiteralParsing, IndexAndDefaultKeyParses) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef int triple [1:3];\n"
              "  triple b = '{1:1, default:0};\n"
              "endmodule\n"));
}

// §5.11 — a type-prefixed array literal is a pattern expression and may appear
// as an expression operand (here a subroutine argument), not only as an
// assignment/declaration target; the explicit prefix supplies its type where no
// assignment-like context is present.
TEST(ArrayLiteralParsing, TypePrefixedLiteralAsExpressionOperand) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef int triple [1:3];\n"
              "  initial $display(triple'{0, 1, 2});\n"
              "endmodule\n"));
}

}  // namespace
