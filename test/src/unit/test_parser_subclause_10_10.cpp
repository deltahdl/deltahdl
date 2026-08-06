#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(UnpackedArrayConcatParsing, ScalarItems) {
  auto r = Parse(
      "module m;\n"
      "  int A[3];\n"
      "  initial A = {1, 2, 3};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(UnpackedArrayConcatParsing, ArrayItems) {
  auto r = Parse(
      "module m;\n"
      "  int A[2], B[2], C[4];\n"
      "  initial C = {A, B};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
}

TEST(UnpackedArrayConcatParsing, EmptyConcat) {
  auto r = Parse(
      "module t;\n"
      "  int q[$];\n"
      "  initial q = {};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
  EXPECT_TRUE(stmt->rhs->elements.empty());
}

// §10.10 allows mixing scalar and array items in a single concatenation, as
// in the LRM example `A9 = {A3, 4, 5, A3, 6};`. The parser shall emit one
// concatenation node holding all five item expressions in source order.
TEST(UnpackedArrayConcatParsing, MixedScalarAndArrayItems) {
  auto r = Parse(
      "module t;\n"
      "  int A3[1:3];\n"
      "  int A9[1:9];\n"
      "  initial A9 = {A3, 4, 5, A3, 6};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kConcatenation);
  ASSERT_EQ(stmt->rhs->elements.size(), 5u);
  EXPECT_EQ(stmt->rhs->elements[0]->kind, ExprKind::kIdentifier);
  EXPECT_EQ(stmt->rhs->elements[0]->text, "A3");
  EXPECT_EQ(stmt->rhs->elements[3]->kind, ExprKind::kIdentifier);
  EXPECT_EQ(stmt->rhs->elements[3]->text, "A3");
}

}  // namespace
