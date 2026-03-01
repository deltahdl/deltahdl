// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- foreach ( ps_or_hierarchical_array_identifier [loop_variables] ) stmt ---
TEST(ParserA608, ForeachStmt) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foreach (arr[i]) $display(arr[i]); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  EXPECT_NE(stmt->expr, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(ParserA608, ForeachSingleVar) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foreach (arr[i]) x = i; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->foreach_vars.size(), 1u);
  EXPECT_EQ(stmt->foreach_vars[0], "i");
}

// §A.6.8: loop_variables — multiple comma-separated identifiers
TEST(ParserA608, ForeachMultipleVars) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foreach (matrix[i, j]) x = i; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->foreach_vars.size(), 2u);
  EXPECT_EQ(stmt->foreach_vars[0], "i");
  EXPECT_EQ(stmt->foreach_vars[1], "j");
}

// §A.6.8: loop_variables — empty slots (skipped dimensions)
TEST(ParserA608, ForeachEmptyVarSlot) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foreach (arr[, j]) x = j; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->foreach_vars.size(), 2u);
  EXPECT_TRUE(stmt->foreach_vars[0].empty());
  EXPECT_EQ(stmt->foreach_vars[1], "j");
}

// §A.6.8: ps_or_hierarchical_array_identifier — hierarchical name
TEST(ParserA608, ForeachHierarchicalArray) {
  auto r = Parse(
      "module m;\n"
      "  initial begin foreach (obj.arr[i]) x = i; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  EXPECT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kMemberAccess);
}

TEST(ParserA608, ForeachBlockBody) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    foreach (arr[i]) begin\n"
      "      x = arr[i];\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

}  // namespace
