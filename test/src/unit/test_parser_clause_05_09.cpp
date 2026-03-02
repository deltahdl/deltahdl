// §5.9: String literals

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// § primary_literal — string_literal
TEST(ParserA84, PrimaryLiteralStringLiteral) {
  auto r = Parse("module m; initial x = \"world\"; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStringLiteral);
}

// --- §5.12 Attributes ---
struct ParseResult512 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult512 Parse(const std::string& src) {
  ParseResult512 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult512& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      if (item->body && item->body->kind == StmtKind::kBlock) {
        return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
      }
      return item->body;
    }
  }
  return nullptr;
}

TEST(ParserCh509, StringLiteral_Basic) {
  auto r = Parse(
      "module m;\n"
      "  initial $display(\"hello world\");\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  ASSERT_GE(stmt->expr->args.size(), 1u);
  EXPECT_EQ(stmt->expr->args[0]->kind, ExprKind::kStringLiteral);
}

TEST(ParserCh509, StringLiteral_Assignment) {
  // A string literal can be assigned to an integral type.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  byte c1;\n"
              "  initial c1 = \"A\";\n"
              "endmodule"));
}

TEST(ParserCh509, StringLiteral_PackedArray) {
  // Storing a string in a packed array, per LRM Section 5.9.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  bit [8*12:1] stringvar = \"Hello world\\n\";\n"
              "endmodule"));
}

TEST(ParserCh509, StringLiteral_InConcatenation) {
  // String concatenation using system task.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display({\"A\", \"B\"});\n"
              "endmodule"));
}

// § constant_primary — primary_literal (string)
TEST(ParserA84, ConstantPrimaryStringLiteral) {
  auto r = Parse("module m; parameter string S = \"hello\"; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* param = r.cu->modules[0]->items[0];
  ASSERT_NE(param->init_expr, nullptr);
  EXPECT_EQ(param->init_expr->kind, ExprKind::kStringLiteral);
}

// § primary — primary_literal (string)
TEST(ParserA84, PrimaryStringLiteral) {
  auto r = Parse("module m; initial x = \"hello\"; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kStringLiteral);
}

}  // namespace
