#include <gtest/gtest.h>

#include <string>

#include "common/diagnostic.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(LexicalConventionParsing, IdentAllLegalChars) {
  auto r = Parse("module m; logic abc_123$xyz; endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "abc_123$xyz");
}

TEST(LexicalConventionParsing, IdentStartsWithUnderscore) {
  auto r = Parse("module m; logic _start_val; endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "_start_val");
}

TEST(LexicalConventionParsing, IdentStartsWithLetter) {
  auto r = Parse("module m; logic Data0; endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "Data0");
}

TEST(LexicalConventionParsing, IdentWithDollarSign) {
  EXPECT_TRUE(ParseOk("module m; logic n$657; endmodule"));
}

TEST(LexicalConventionParsing, CaseSensitive) {
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

TEST(LexicalConventionParsing, NumberFollowedByIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  initial x = 42 + abc;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto* rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kIntegerLiteral);
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

TEST(LexicalConventionParsing, LetIdentUnderscore) {
  auto r = Parse(
      "module m;\n"
      "  let _my_let_123 = 0;\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "_my_let_123");
}

TEST(LexicalConventionParsing, IdentifierAsModuleName) {
  auto r = Parse("module my_mod_99; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "my_mod_99");
}

TEST(LexicalConventionParsing, IdentifierAsPortName) {
  auto r = Parse("module m(input logic _data_in); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(LexicalConventionParsing, MaxLengthIdentifierParses) {
  std::string long_id(1024, 'z');
  auto r = Parse("module m; logic " + long_id + "; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(LexicalConventionParsing, IdentifierInAssignExpression) {
  auto r = Parse(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  assign a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(LexicalConventionParsing, KeywordCannotBeUsedAsIdentifier) {
  auto r = Parse("module m; logic module; endmodule");
  // §6.8 states the variable declaration whose declarator the keyword stands
  // in, and Parser::ParseVarDeclList files the report under it.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got 'module'", 1, "6.8"));
}

TEST(LexicalConventionParsing, IdentifierExceedingMaxLengthReportsError) {
  std::string long_id(1025, 'a');
  auto r = Parse("module m; logic " + long_id + "; endmodule");
  EXPECT_TRUE(ReportedError(
      r.diags, "identifier exceeds maximum length of 1024 characters", 1,
      "5.6"));
}

// §5.6 has the first character of a simple identifier be a letter or an
// underscore, never a `$`. The lexer makes `$dollar` a system identifier, the
// only thing those characters can be; where a name is expected, the report is
// the lexical rule the spelling breaks, not the declaration grammar around it.
TEST(LexicalConventionParsing, NameBeginningWithDollarIsReportedUnderClause56) {
  auto r = Parse(
      "module identifiers();\n"
      "  reg $dollar;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "identifier '$dollar' shall not begin with '$'", 2, "5.6"));
}

// The same rule for a digit: `0number` is the integer 0 with the identifier
// number directly against it, and that adjacency is what makes it one
// misspelt name rather than two tokens the grammar has other uses for.
TEST(LexicalConventionParsing, NameBeginningWithDigitIsReportedUnderClause56) {
  auto r = Parse(
      "module identifiers();\n"
      "  reg $dollar;\n"
      "  reg 0number;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "identifier '0number' shall not begin with a digit", 3, "5.6"));
}

// With white space between them, `0` and `number` are the two tokens they
// look like and no name beginning with a digit was written: the declaration
// is still wrong, but under its own grammar, not under §5.6.
TEST(LexicalConventionParsing, DigitThenSpaceThenNameIsNotAClause56Report) {
  auto r = Parse(
      "module m;\n"
      "  reg 0 number;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
  EXPECT_FALSE(
      ReportedError(r.diags, "shall not begin with a digit", 2, "5.6"));
  EXPECT_TRUE(ReportedError(r.diags, "expected identifier, got integer literal",
                            2, "6.8"));
}

// The misspelt name is taken as the declarator so that the rest of the
// declaration is parsed in step: one report for the name, none for the
// declaration or the module body around it.
TEST(LexicalConventionParsing,
     MisspeltNameIsTakenAsTheDeclaratorWithoutCascade) {
  auto r = Parse(
      "module identifiers();\n"
      "  reg $dollar;\n"
      "  reg 0number;\n"
      "endmodule\n");
  for (const auto& d : r.diags) {
    EXPECT_EQ(d.message.find("expected identifier"), std::string::npos)
        << d.message;
    EXPECT_EQ(d.message.find("unexpected token in module body"),
              std::string::npos)
        << d.message;
  }
}

}  // namespace
