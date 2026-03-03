// §10.4: Procedural assignments

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

// =============================================================================
// Integration: Mixing blocking and nonblocking in the same block
// =============================================================================
TEST(ParserA602, MixedAssignments_BlockingAndNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b <= 2;\n"
      "    c += 3;\n"
      "    d <= #10 4;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto stmts = AllInitialStmts(r);
  ASSERT_EQ(stmts.size(), 4u);
  EXPECT_EQ(stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmts[1]->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(stmts[2]->kind, StmtKind::kBlockingAssign);  // compound
  EXPECT_EQ(stmts[3]->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmts[3]->delay, nullptr);
}

struct ParseResult4b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ModuleItem* FindItemByKind(ParseResult4b& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

static ModuleItem* FindInitialBlock(ParseResult4b& r) {
  return FindItemByKind(r, ModuleItemKind::kInitialBlock);
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

// ---------------------------------------------------------------------------
// 7. Mix of blocking and non-blocking assignments
// ---------------------------------------------------------------------------
TEST(ParserSection4, Sec4_5_MixBlockingNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b, c, d;\n"
      "  initial begin\n"
      "    a = b;\n"
      "    c <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* init_item = FindInitialBlock(r);
  ASSERT_NE(init_item, nullptr);
  auto* body = init_item->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kNonblockingAssign);
}

}  // namespace
