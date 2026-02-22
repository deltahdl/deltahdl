#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

Stmt *FirstInitialStmt(ParseResult &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

}  // namespace

// =============================================================================
// Annex D -- Optional system tasks
// =============================================================================

TEST(ParserAnnexD, AnnexDCountdrivers) {
  auto r = Parse("module m; initial $countdrivers(sig); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
}

TEST(ParserAnnexD, AnnexDList) {
  auto r = Parse("module m; initial $list; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
}

TEST(ParserAnnexD, AnnexDLog) {
  auto r = Parse(
      "module m;\n"
      "  initial begin $log(\"sim.log\"); $nolog; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserAnnexD, AnnexDSave) {
  auto r = Parse(
      "module m;\n"
      "  initial begin $save(\"s.sav\"); $restart(\"s.sav\"); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserAnnexD, AnnexDScope) {
  auto r = Parse(
      "module m;\n"
      "  initial begin $scope(m); $showscopes; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}
