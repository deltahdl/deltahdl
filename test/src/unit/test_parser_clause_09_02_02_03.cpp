// §9.2.2.3: Latched logic always_latch procedure

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

// Return all statements from the first initial block's begin/end.
static std::vector<Stmt*> AllInitialStmts(ParseResult& r) {
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  if (!item || !item->body) return {};
  if (item->body->kind == StmtKind::kBlock) return item->body->stmts;
  return {item->body};
}

namespace {

TEST(ParserA602, AlwaysConstruct_AlwaysLatch) {
  auto r = Parse(
      "module m;\n"
      "  always_latch\n"
      "    if (en) q = d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysLatch);
}

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

// ---------------------------------------------------------------------------
// 30. Three always_latch blocks in same module, counting them all.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_ThreeAlwaysLatchBlocks) {
  auto r = Parse(
      "module m;\n"
      "  logic en, d1, d2, d3, q1, q2, q3;\n"
      "  always_latch\n"
      "    if (en) q1 <= d1;\n"
      "  always_latch\n"
      "    if (en) q2 <= d2;\n"
      "  always_latch\n"
      "    if (en) q3 <= d3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      ++count;
      EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysLatch);
      EXPECT_TRUE(item->sensitivity.empty());
      ASSERT_NE(item->body, nullptr);
      EXPECT_EQ(item->body->kind, StmtKind::kIf);
    }
  }
  EXPECT_EQ(count, 3);
}

struct ParseResult9i {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9i Parse(const std::string& src) {
  ParseResult9i result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FirstAlwaysLatchItem(ParseResult9i& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysLatchBlock) return item;
  }
  return nullptr;
}

// =============================================================================
// LRM section 9.2.3 -- Always_latch procedure
//
// The always_latch procedure models latched logic.  It has an implicit
// sensitivity list (no @(...) clause) and is expected to infer latches.
// =============================================================================
// ---------------------------------------------------------------------------
// 1. Simple if-else latch pattern -- the canonical always_latch usage.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_SimpleIfElseLatch) {
  auto r = Parse(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch\n"
      "    if (en) q <= d;\n"
      "    else q <= q;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysLatchBlock);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysLatch);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kIf);
  EXPECT_NE(item->body->then_branch, nullptr);
  EXPECT_NE(item->body->else_branch, nullptr);
}

// ---------------------------------------------------------------------------
// 2. always_latch with begin-end block wrapping the body.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_3_BeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  logic en, d, q;\n"
      "  always_latch begin\n"
      "    if (en) q <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysLatchItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysLatchBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kIf);
}

}  // namespace
