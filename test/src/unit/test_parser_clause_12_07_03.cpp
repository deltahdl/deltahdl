// §12.7.3: The foreach-loop

#include "fixture_parser.h"

using namespace delta;

struct ParseResult9h {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9h Parse(const std::string& src) {
  ParseResult9h result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// ---------------------------------------------------------------------------
// 10. always_comb with foreach loop
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_ForeachLoop) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] arr [0:3];\n"
      "  logic [7:0] inv [0:3];\n"
      "  always_comb begin\n"
      "    foreach (arr[i])\n"
      "      inv[i] = ~arr[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstAlwaysCombStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  ASSERT_FALSE(stmt->foreach_vars.empty());
}

// =============================================================================
// LRM section 12.7.3 -- foreach loop
// =============================================================================
TEST(ParserSection12, ForeachBasicParses) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    foreach (arr[i]) x = arr[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  EXPECT_NE(stmt->expr, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(ParserSection12, ForeachBasicVars) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    foreach (arr[i]) x = arr[i];\n"
      "  end\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->foreach_vars.size(), 1u);
  EXPECT_EQ(stmt->foreach_vars[0], "i");
}

TEST(ParserSection12, ForeachEmptyVar) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    foreach (arr[, j]) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  ASSERT_EQ(stmt->foreach_vars.size(), 2u);
}

TEST(ParserSection12, ForeachEmptyVarValues) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    foreach (arr[, j]) x = 1;\n"
      "  end\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_TRUE(stmt->foreach_vars[0].empty());
  EXPECT_EQ(stmt->foreach_vars[1], "j");
}

TEST(ParserSection12, ForeachWithBlock) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    foreach (arr[i]) begin\n"
      "      $display(\"%d\", arr[i]);\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

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
