// §5.6: Identifiers, keywords, and system names

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA212, LetIdentifier_Underscore) {
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

// =========================================================================
// Identifiers with all legal characters: letters, digits, _, $
// =========================================================================
TEST(ParserCh501, Sec5_1_IdentifierAllLegalChars) {
  // An identifier may contain letters, digits, underscore, and dollar sign.
  auto r = Parse("module m; logic abc_123$xyz; endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "abc_123$xyz");
}

// =========================================================================
// Simple identifiers starting with underscore
// =========================================================================
TEST(ParserCh501, Sec5_1_IdentifierStartsWithUnderscore) {
  auto r = Parse("module m; logic _start_val; endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "_start_val");
}

// =========================================================================
// Identifiers starting with letter
// =========================================================================
TEST(ParserCh501, Sec5_1_IdentifierStartsWithLetter) {
  auto r = Parse("module m; logic Data0; endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "Data0");
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

// =========================================================================
// Number followed by identifier (separate tokens)
// =========================================================================
TEST(ParserCh501, Sec5_1_NumberFollowedByIdentifier) {
  // "42" and "abc" are separate tokens even without whitespace between the
  // numeric literal and an identifier in expression context.
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
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "_bus3");
}

TEST(ParserCh506, Ident_SimpleWithDollarSign) {
  EXPECT_TRUE(ParseOk("module m; logic n$657; endmodule"));
}

}  // namespace
