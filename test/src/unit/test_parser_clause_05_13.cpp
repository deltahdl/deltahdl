// §5.13: Built-in methods

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

// --- §5.13 Built-in methods ---
namespace {

TEST(ParserCh513, BuiltInMethodCall_ChainedAccess) {
  // Chained member access: obj.arr.size() parses as a call.
  auto r = Parse(
      "module t;\n"
      "  initial x = obj.arr.size();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

// From test_parser_clause_05b.cpp
TEST(ParserCh513, BuiltInMethod_NoParens) {
  // When a method has no arguments the parentheses are optional.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  int q[$];\n"
              "  initial x = q.size;\n"
              "endmodule"));
}

}  // namespace
