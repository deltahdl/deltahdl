// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

struct ParseResult9k {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9k Parse(const std::string& src) {
  ParseResult9k result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult9k& r) {
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

// ---------------------------------------------------------------------------
// iff guard at statement level inside initial (populates Stmt::events)
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_4_2_4_IffGuardStmtLevel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk iff en) q <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_NE(stmt->events[0].iff_condition, nullptr);
}

}  // namespace
