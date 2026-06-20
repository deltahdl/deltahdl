#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(QueueOpsParsing, SliceWithVariableBounds) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  int dst[$];\n"
      "  int a, b;\n"
      "  initial dst = {q[a:b]};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(QueueOpsParsing, SliceWithExpressionBounds) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  int dst[$];\n"
      "  int i;\n"
      "  initial dst = {q[i+1:i+3]};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(QueueOpsParsing, SliceWithDollarBound) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  int dst[$];\n"
      "  initial dst = {q[0:$]};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(QueueOpsParsing, IndexedWriteParsed) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  initial q[0] = 42;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

TEST(QueueOpsParsing, EmptyConcatAssign) {
  auto r = Parse(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = {};\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
