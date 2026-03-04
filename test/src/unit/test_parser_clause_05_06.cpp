// §5.6: Identifiers, keywords, and system names

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA212, LetIdentifier_Underscore) {
  auto r = Parse("module m;\n"
                 "  let _my_let_123 = 0;\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto *item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kLetDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "_my_let_123");
}

// =========================================================================
// Section 5.6: Identifiers, keywords, and system names
// =========================================================================
// =========================================================================
// Section 5.6.3: System tasks and system functions
// =========================================================================
// =========================================================================
// Identifiers with all legal characters: letters, digits, _, $
// =========================================================================
TEST(ParserCh501, Sec5_1_IdentifierAllLegalChars) {
  // An identifier may contain letters, digits, underscore, and dollar sign.
  auto r = Parse("module m; logic abc_123$xyz; endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "abc_123$xyz");
}

// =========================================================================
// Simple identifiers starting with underscore
// =========================================================================
TEST(ParserCh501, Sec5_1_IdentifierStartsWithUnderscore) {
  auto r = Parse("module m; logic _start_val; endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "_start_val");
}

// =========================================================================
// Identifiers starting with letter
// =========================================================================
TEST(ParserCh501, Sec5_1_IdentifierStartsWithLetter) {
  auto r = Parse("module m; logic Data0; endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "Data0");
}
// =========================================================================
// Number followed by identifier (separate tokens)
// =========================================================================
TEST(ParserCh501, Sec5_1_NumberFollowedByIdentifier) {
  // "42" and "abc" are separate tokens even without whitespace between the
  // numeric literal and an identifier in expression context.
  auto r = Parse("module m;\n"
                 "  initial x = 42 + abc;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  auto *rhs = stmt->rhs;
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  EXPECT_EQ(rhs->op, TokenKind::kPlus);
  // LHS should be integer literal 42.
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(rhs->lhs->int_val, 42u);
  // RHS should be identifier abc.
  ASSERT_NE(rhs->rhs, nullptr);
  EXPECT_EQ(rhs->rhs->kind, ExprKind::kIdentifier);
}

TEST(ParserCh506, Ident_SimpleWithUnderscore) {
  auto r = Parse("module m; logic _bus3; endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "_bus3");
}

TEST(ParserCh506, Ident_SimpleWithDollarSign) {
  EXPECT_TRUE(ParseOk("module m; logic n$657; endmodule"));
}

TEST(ParserCh506, Ident_CaseSensitive) {
  // Identifiers are case sensitive: X and x are different.
  auto r = Parse("module m;\n"
                 "  logic X;\n"
                 "  logic x;\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "X");
  EXPECT_EQ(r.cu->modules[0]->items[1]->name, "x");
}

} // namespace
