#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// =========================================================================
// Section 5.8: Time literals
// =========================================================================

struct ParseResult508 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult508 Parse(const std::string &src) {
  ParseResult508 result;
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

static Stmt *FirstInitialStmt(ParseResult508 &r) {
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

TEST(ParserCh508, TimeLiteral_IntegerNs) {
  auto r = Parse(
      "module m;\n"
      "  initial #40ns;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
}

TEST(ParserCh508, TimeLiteral_FixedPointNs) {
  // 2.1ns -- a time literal with a fixed-point value.
  EXPECT_TRUE(ParseOk("module m; initial #2.1ns; endmodule"));
}

TEST(ParserCh508, TimeLiteral_Ps) {
  EXPECT_TRUE(ParseOk("module m; initial #40ps; endmodule"));
}

TEST(ParserCh508, TimeLiteral_Us) {
  EXPECT_TRUE(ParseOk("module m; initial #100us; endmodule"));
}

TEST(ParserCh508, TimeLiteral_Ms) {
  EXPECT_TRUE(ParseOk("module m; initial #1ms; endmodule"));
}

TEST(ParserCh508, TimeLiteral_Fs) {
  EXPECT_TRUE(ParseOk("module m; initial #500fs; endmodule"));
}
