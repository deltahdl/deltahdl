#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(BuiltInMethodParsing, BuiltInMethodCall_Parse) {
  auto r = Parse(
      "module t;\n"
      "  initial x = arr.size();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

TEST(BuiltInMethodParsing, BuiltInMethodCall_Callee) {
  auto r = Parse(
      "module t;\n"
      "  initial x = arr.size();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kMemberAccess);
}

TEST(DynamicArrayAndQueueParsing, DynamicArraySize) {
  auto r = Parse(
      "module m;\n"
      "  int dyn[];\n"
      "  int sz;\n"
      "  initial begin\n"
      "    dyn = new[5];\n"
      "    sz = dyn.size();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AggregateTypeParsing, DynamicArraySizeMethod) {
  auto r = Parse(
      "module t;\n"
      "  int dyn[];\n"
      "  initial x = dyn.size();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kCall);
}

}  // namespace
