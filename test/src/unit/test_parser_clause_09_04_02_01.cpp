// §9.4.2.1: Event OR operator

#include "fixture_parser.h"

using namespace delta;

struct ParseResult9d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9d Parse(const std::string& src) {
  ParseResult9d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* FirstInitialBody(ParseResult9d& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) return item->body;
  }
  return nullptr;
}

static Stmt* FirstInitialStmt(ParseResult9d& r) {
  auto* body = FirstInitialBody(r);
  if (body && body->kind == StmtKind::kBlock) {
    return body->stmts.empty() ? nullptr : body->stmts[0];
  }
  return body;
}

namespace {

TEST(ParserSection9c, EventControlMultipleOrExpressions) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(a or b or c) x = a + b + c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_GE(stmt->events.size(), 3u);
}

TEST(ParserSection9c, EventControlMixedEdgesComma) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk, negedge rst, a) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_GE(stmt->events.size(), 3u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_EQ(stmt->events[1].edge, Edge::kNegedge);
  EXPECT_EQ(stmt->events[2].edge, Edge::kNone);
}

struct ParseResult4c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult4c Parse(const std::string& src) {
  ParseResult4c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// Returns the first always_* item from the first module.
static ModuleItem* FirstAlwaysItem(ParseResult4c& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock ||
        item->kind == ModuleItemKind::kAlwaysBlock)
      return item;
  }
  return nullptr;
}

// ---------------------------------------------------------------------------
// 29. Multiple event control in always block
// ---------------------------------------------------------------------------
TEST(ParserSection4, Sec4_5_MultipleEventControlInAlways) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, rst, a;\n"
      "  always @(posedge clk or negedge rst) begin\n"
      "    if (!rst)\n"
      "      a <= 0;\n"
      "    else\n"
      "      a <= 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->sensitivity.size(), 2u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_EQ(item->sensitivity[1].edge, Edge::kNegedge);
}

// §9.4.2.1: or-separated event list
TEST(ParserA605, EventExprOr) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk_a or posedge clk_b) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 2u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_EQ(stmt->events[1].edge, Edge::kPosedge);
}

}  // namespace
