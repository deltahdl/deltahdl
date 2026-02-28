// §9.4.2.2: Implicit event_expression list

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

TEST(ParserA602, AlwaysConstruct_ImplicitSensitivityStar) {
  // @* implicit sensitivity
  auto r = Parse(
      "module m;\n"
      "  always @* y = a + b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(item, nullptr);
}

TEST(ParserA602, AlwaysConstruct_ImplicitSensitivityParenStar) {
  // @(*) implicit sensitivity
  auto r = Parse(
      "module m;\n"
      "  always @(*) y = a + b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(item, nullptr);
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

static ModuleItem* FirstAlwaysItem(ParseResult9k& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      return item;
    }
  }
  return nullptr;
}

// =============================================================================
// LRM section 9.4.2.3 -- Implicit event_expression list (@* and @(*))
// =============================================================================
// @* at always block level: always @* stmt
TEST(ParserSection9, Sec9_4_2_3_AtStarAlwaysSimple) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  always @* a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
}

// @(*) at always block level: always @(*) stmt
TEST(ParserSection9, Sec9_4_2_3_AtStarParenAlwaysSimple) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  always @(*) a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
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

// @* at statement level inside initial: produces kEventControl with
// is_star_event=true
TEST(ParserSection9, Sec9_4_2_3_AtStarStmtLevelInitial) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    @* a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_TRUE(stmt->events.empty());
}

// Helper for blocks 11: verify always block has var decl body.
static void VerifyAlwaysVarDecl(ParseResult& r) {
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 3u);
  EXPECT_EQ(item->body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(item->body->stmts[0]->var_name, "temp");
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

// ---------------------------------------------------------------------------
// 20. always @* with variable declarations in begin-end block.
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_2_2_2_AlwaysStarVarDecls) {
  auto r = Parse(
      "module m;\n"
      "  always @* begin\n"
      "    int temp;\n"
      "    temp = a + b;\n"
      "    y = temp;\n"
      "  end\n"
      "endmodule\n");
  VerifyAlwaysVarDecl(r);
}

// @(*) at statement level: produces kEventControl with is_star_event=true
TEST(ParserSection9, Sec9_4_2_3_AtStarParenStmtLevel) {
  auto r = Parse(
      "module m;\n"
      "  reg a, b;\n"
      "  initial begin\n"
      "    @(*) a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_TRUE(stmt->events.empty());
}

}  // namespace
