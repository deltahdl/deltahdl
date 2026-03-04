#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ParserSection11, StreamingRightDetails) {
  auto r = Parse(
      "module t;\n"
      "  initial x = {>> {a, b, c}};\n"
      "endmodule\n");
  auto* rhs = FirstAssignRhs(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->op, TokenKind::kGtGt);
  EXPECT_EQ(rhs->elements.size(), 3u);
}

TEST(ParserA81, StreamConcatMultipleElements) {
  auto r = Parse("module m; initial x = {<< {a, b, c}}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->rhs->kind, ExprKind::kStreamingConcat);
  EXPECT_EQ(stmt->rhs->elements.size(), 3u);
}

}
