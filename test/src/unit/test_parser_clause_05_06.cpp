#include <string>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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

// §3.1 — Module with design element name containing underscores and digits.
TEST(CompilationUnitStructure, DesignElementNameWithUnderscoresAndDigits) {
  auto r = Parse("module my_module_123; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "my_module_123");
}

// §5.6: "A keyword (see 5.6.2) may not be used as a user-defined identifier."
// In a position where the parser expects an identifier, a keyword token must
// cause a parse error rather than being accepted as a name.
TEST(LexicalConventionParsing, KeywordCannotBeUsedAsIdentifier) {
  auto r = Parse("module m; logic module; endmodule");
  EXPECT_TRUE(r.has_errors);
}

// §5.6: "If an identifier exceeds the implementation-specific length limit,
// an error shall be reported." The lexer-stage error must reach the parser's
// diagnostic engine when source containing a 1025-character identifier is
// parsed.
TEST(LexicalConventionParsing, IdentifierExceedingMaxLengthReportsError) {
  std::string long_id(1025, 'a');
  auto r = Parse("module m; logic " + long_id + "; endmodule");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
