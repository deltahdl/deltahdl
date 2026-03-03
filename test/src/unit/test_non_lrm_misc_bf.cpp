// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

// =========================================================================
// Section 5.6: Identifiers, keywords, and system names
// =========================================================================
struct ParseResult506 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ModuleItem* FirstItem(ParseResult506& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

// =========================================================================
// Section 5.6.3: System tasks and system functions
// =========================================================================
struct ParseResult50603 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult50603 Parse(const std::string& src) {
  ParseResult50603 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult50603& r) {
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

namespace {

TEST(ParserCh505, Operator_UnaryBitwiseNegate) {
  auto r = Parse(
      "module m;\n"
      "  initial x = ~y;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kTilde);
}

TEST(ParserCh505, Operator_BinaryAdd) {
  auto r = Parse(
      "module m;\n"
      "  initial x = a + b;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
}

TEST(ParserCh505, Operator_Ternary) {
  auto r = Parse(
      "module m;\n"
      "  initial x = sel ? a : b;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kTernary);
  ASSERT_NE(rhs->condition, nullptr);
  ASSERT_NE(rhs->true_expr, nullptr);
  ASSERT_NE(rhs->false_expr, nullptr);
}

TEST(ParserCh505, Operator_LogicalShiftLeft) {
  EXPECT_TRUE(ParseOk("module m; initial x = a <<< 2; endmodule"));
}

TEST(ParserCh505, Operator_ArithShiftRight) {
  EXPECT_TRUE(ParseOk("module m; initial x = a >>> 1; endmodule"));
}

TEST(ParserCh505, Operator_CaseEquality) {
  // === is the case equality operator.
  auto r = Parse(
      "module m;\n"
      "  initial x = (a === b);\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kEqEqEq);
}

TEST(ParserCh505, Operator_CaseInequality) {
  // !== is the case inequality operator.
  EXPECT_TRUE(ParseOk("module m; initial x = (a !== b); endmodule"));
}

TEST(ParserCh505, Operator_ReductionAnd) {
  auto r = Parse(
      "module m;\n"
      "  initial x = &y;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kUnary);
  EXPECT_EQ(rhs->op, TokenKind::kAmp);
}

TEST(ParserCh505, Operator_ReductionXnor) {
  EXPECT_TRUE(ParseOk("module m; initial x = ~^y; endmodule"));
}

TEST(ParserCh505, Operator_Power) {
  EXPECT_TRUE(ParseOk("module m; initial x = 2 ** 10; endmodule"));
}

TEST(ParserCh505, Operator_WildcardEquality) {
  // ==? is the wildcard equality operator.
  EXPECT_TRUE(ParseOk("module m; initial x = (a ==? b); endmodule"));
}

TEST(ParserCh506, Ident_SimpleWithUnderscore) {
  auto r = Parse("module m; logic _bus3; endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "_bus3");
}

TEST(ParserCh506, Ident_SimpleWithDollarSign) {
  EXPECT_TRUE(ParseOk("module m; logic n$657; endmodule"));
}

TEST(ParserCh506, Ident_CaseSensitive) {
  // Identifiers are case sensitive: X and x are different.
  auto r = Parse(
      "module m;\n"
      "  logic X;\n"
      "  logic x;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "X");
  EXPECT_EQ(r.cu->modules[0]->items[1]->name, "x");
}

// From test_parser_clause_05.cpp
TEST(ParserCh50601, EscapedIdentifierAsName) {
  // §5.6.1: escaped identifiers include special characters.
  EXPECT_TRUE(ParseOk("module t; wire \\bus+index ; endmodule"));
}

TEST(ParserCh50601, EscapedKeywordAsIdentifier) {
  // §5.6.1: escaped keyword is treated as a user-defined identifier.
  EXPECT_TRUE(ParseOk("module t; wire \\module ; endmodule"));
}

// From test_parser_clause_05b.cpp
TEST(ParserCh50601, EscapedIdent_Basic) {
  EXPECT_TRUE(ParseOk("module m; wire \\busa+index ; endmodule"));
}

TEST(ParserCh50601, EscapedIdent_Keyword) {
  // An escaped keyword is treated as a user-defined identifier, not as a
  // keyword. \net is a valid user-defined wire name.
  EXPECT_TRUE(ParseOk("module m; wire \\net ; endmodule"));
}

TEST(ParserCh50601, EscapedIdent_SpecialChars) {
  // Escaped identifiers can contain any printable ASCII character.
  EXPECT_TRUE(ParseOk("module m; wire \\***error-condition*** ; endmodule"));
}

TEST(ParserCh50601, EscapedIdent_ForwardSlash) {
  // \net1/\net2 is a valid escaped identifier containing a slash.
  EXPECT_TRUE(ParseOk("module m; wire \\net1/\\net2 ; endmodule"));
}

TEST(ParserCh50601, EscapedIdent_Braces) {
  // \{a,b} is a valid escaped identifier containing braces.
  EXPECT_TRUE(ParseOk("module m; wire \\{a,b} ; endmodule"));
}

// From test_parser_clause_05b.cpp
TEST(ParserCh50602, Keyword_EscapedAsIdentifier) {
  // An escaped keyword should be treated as a user-defined identifier.
  EXPECT_TRUE(ParseOk("module m; logic \\begin ; endmodule"));
}

TEST(ParserCh50602, Keyword_AllLowercase) {
  // Keywords are lowercase only; MODULE is not a keyword, so this fails.
  EXPECT_FALSE(ParseOk("MODULE m; endmodule"));
}

TEST(ParserCh50603, SystemTask_Display) {
  // $display is a system task call (Section 5.6.3, Section 21.2).
  auto r = Parse(
      "module m;\n"
      "  initial $display(\"hello\");\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
}

}  // namespace
