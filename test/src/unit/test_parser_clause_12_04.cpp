// §12.4: Conditional if–else statement

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

struct ParseResult12b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult12b Parse(const std::string& src) {
  ParseResult12b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult12b& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

namespace {

TEST(ParserSection12, NestedIfElse) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a)\n"
      "      if (b) x = 1;\n"
      "      else x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  // Else associates with the inner if
  EXPECT_EQ(stmt->else_branch, nullptr);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kIf);
  EXPECT_NE(stmt->then_branch->else_branch, nullptr);
}

TEST(ParserSection12, IfWithBlockBody) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a) begin\n"
      "      x = 1;\n"
      "      y = 2;\n"
      "    end else begin\n"
      "      x = 3;\n"
      "      y = 4;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kBlock);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kBlock);
}

// =============================================================================
// A.6.6 Conditional statements
// =============================================================================
// ---------------------------------------------------------------------------
// conditional_statement ::=
//   [ unique_priority ] if ( cond_predicate ) statement_or_null
//   { else if ( cond_predicate ) statement_or_null }
//   [ else statement_or_null ]
// ---------------------------------------------------------------------------
// §12.4: basic if statement — true branch only, no else
TEST(ParserA606, IfOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial begin if (a) x = 1; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->else_branch, nullptr);
}

// §12.4: if-else statement
TEST(ParserA606, IfElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin if (a) x = 1; else x = 0; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->then_branch, nullptr);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kBlockingAssign);
}

// =============================================================================
// LRM section 12.4 -- Conditional if-else statement
// =============================================================================
// Basic if without else -- verifies condition/branch pointers.
TEST(ParserSection12, IfNoElseConditionAndBranches) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->else_branch, nullptr);
}

// §12.4: if with null statement_or_null (semicolon) for then branch
TEST(ParserA606, IfNullThen) {
  auto r = Parse(
      "module m;\n"
      "  initial begin if (a) ; else x = 0; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kNull);
  ASSERT_NE(stmt->else_branch, nullptr);
}

// If-else with both branches.
TEST(ParserSection12, IfWithElse) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a) x = 1;\n"
      "    else x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_NE(stmt->else_branch, nullptr);
}

// §12.4: if with null else branch
TEST(ParserA606, IfNullElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin if (a) x = 1; else ; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kNull);
}

// §12.4: if with begin-end block in both branches
TEST(ParserA606, IfElseWithBlocks) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (cond) begin\n"
      "      x = 1;\n"
      "      y = 2;\n"
      "    end else begin\n"
      "      x = 3;\n"
      "      y = 4;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kBlock);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kBlock);
}

// If with begin-end block body (then-only).
TEST(ParserSection12, IfBlockBodyThenOnly) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a) begin\n"
      "      x = 1;\n"
      "      y = 2;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kBlock);
}

// §12.4: dangling else associates with closest if
TEST(ParserA606, DanglingElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a)\n"
      "      if (b) x = 1;\n"
      "      else x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  // outer if has no else — the else belongs to the inner if
  EXPECT_EQ(stmt->else_branch, nullptr);
  // then_branch is the inner if, which has an else
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kIf);
  EXPECT_NE(stmt->then_branch->else_branch, nullptr);
}

// §12.4: forced else association with begin-end
TEST(ParserA606, ForcedElseWithBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a) begin\n"
      "      if (b) x = 1;\n"
      "    end\n"
      "    else x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  // outer if now has else (because begin-end blocks inner if)
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kBlockingAssign);
  // then_branch is a block containing inner if with no else
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kBlock);
}

// Plain if (no qualifier) has kNone qualifier.
TEST(ParserSection12, PlainIfHasNoQualifier) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a) x = 1;\n"
      "    else x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->qualifier, CaseQualifier::kNone);
}

// ---------------------------------------------------------------------------
// Structural tests: nested conditionals, complex conditions
// ---------------------------------------------------------------------------
// §12.4: nested if inside begin-end
TEST(ParserA606, NestedIfInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (a) begin\n"
      "      if (b) x = 1;\n"
      "      else x = 2;\n"
      "    end else begin\n"
      "      if (c) x = 3;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  // both branches are blocks
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kBlock);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kBlock);
}

// §12.4: complex condition expression
TEST(ParserA606, ComplexCondExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if ((a > 0) && (b < 10) || c) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
}

// §12.4: if condition with function call
TEST(ParserA606, IfCondFunctionCall) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if ($unsigned(a) > 0) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
}

struct ParseResult10d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult10d Parse(const std::string& src) {
  ParseResult10d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult10d& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

// --- 28. Blocking assignment in nested if-else with expressions ---
TEST(ParserSection10, Sec10_4_1_NestedIfElseWithExpressions) {
  auto r = Parse(
      "module m;\n"
      "  reg [7:0] out, a, b;\n"
      "  reg sel1, sel2;\n"
      "  initial begin\n"
      "    if (sel1)\n"
      "      if (sel2)\n"
      "        out = a + b;\n"
      "      else\n"
      "        out = a - b;\n"
      "    else\n"
      "      out = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->then_branch->kind, StmtKind::kIf);
  EXPECT_EQ(stmt->then_branch->then_branch->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->then_branch->then_branch->rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(stmt->then_branch->else_branch->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->then_branch->else_branch->rhs->kind, ExprKind::kBinary);
  ASSERT_NE(stmt->else_branch, nullptr);
  EXPECT_EQ(stmt->else_branch->kind, StmtKind::kBlockingAssign);
}

// §12.4: conditional_statement (if-else)
TEST(ParserA604, StmtItemConditionalStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (x) a = 1; else a = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
}

// =============================================================================
// LRM section 12.4 -- Conditional if-else statement
// =============================================================================
TEST(ParserSection12, BasicIfElse) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a) x = 1;\n"
      "    else x = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
  ASSERT_NE(stmt->then_branch, nullptr);
  ASSERT_NE(stmt->else_branch, nullptr);
}

TEST(ParserSection12, IfWithoutElse) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    if (a) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_EQ(stmt->else_branch, nullptr);
}

}  // namespace
