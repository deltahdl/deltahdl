#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// =========================================================================
// Section 5.9: String literals
// =========================================================================

struct ParseResult509 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult509 Parse(const std::string &src) {
  ParseResult509 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static Stmt *FirstInitialStmt(ParseResult509 &r) {
  for (auto *item : r.cu->modules[0]->items) {
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
  auto r = Parse("module m;\n"
                 "  initial $display(\"hello world\");\n"
                 "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  ASSERT_GE(stmt->expr->args.size(), 1u);
  EXPECT_EQ(stmt->expr->args[0]->kind, ExprKind::kStringLiteral);
}

TEST(ParserCh509, StringLiteral_Assignment) {
  // A string literal can be assigned to an integral type.
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  byte c1;\n"
                      "  initial c1 = \"A\";\n"
                      "endmodule"));
}

TEST(ParserCh509, StringLiteral_PackedArray) {
  // Storing a string in a packed array, per LRM Section 5.9.
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  bit [8*12:1] stringvar = \"Hello world\\n\";\n"
                      "endmodule"));
}

TEST(ParserCh509, StringLiteral_AsParameter) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  parameter string MSG = \"default message\";\n"
                      "endmodule"));
}

TEST(ParserCh509, StringLiteral_InConcatenation) {
  // String concatenation using system task.
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  initial $display({\"A\", \"B\"});\n"
                      "endmodule"));
}
