// §9.3.4: Block names

#include "fixture_parser.h"

using namespace delta;

namespace {

// Checker with end label.
TEST(SourceText, CheckerEndLabel) {
  auto r = Parse("checker chk; endchecker : chk\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

static Stmt* InitialBody(ParseResult& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    return item->body;
  }
  return nullptr;
}

// §9.3.4: Named sequential block
TEST(ParserA603, SeqBlockNamed) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : my_block\n"
      "    a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "my_block");
}

// §9.3.4: Named sequential block with matching end label
TEST(ParserA603, SeqBlockNamedWithEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : blockB\n"
      "    a = 1;\n"
      "  end : blockB\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "blockB");
}

// §9.3.4: Named fork block
TEST(ParserA603, ForkNamed) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : my_fork\n"
      "      #10 a = 1;\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "my_fork");
}

// §9.3.4: Named fork block with matching end label
TEST(ParserA603, ForkNamedWithEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : my_fork\n"
      "      #10 a = 1;\n"
      "    join : my_fork\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->label, "my_fork");
}

// §9.3.4: Named fork with join_any and end label
TEST(ParserA603, ForkNamedJoinAnyWithEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : f1\n"
      "      #10 a = 1;\n"
      "    join_any : f1\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinAny);
  EXPECT_EQ(stmt->label, "f1");
}

// §9.3.4: Named fork with join_none and end label
TEST(ParserA603, ForkNamedJoinNoneWithEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : f2\n"
      "      #10 a = 1;\n"
      "    join_none : f2\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinNone);
  EXPECT_EQ(stmt->label, "f2");
}

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

TEST(ParserSection9c, SequentialBlockNamedWithDecls) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : my_block\n"
      "    integer count;\n"
      "    count = 0;\n"
      "  end : my_block\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "my_block");
}

struct ParseResult4d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult4d Parse(const std::string& src) {
  ParseResult4d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// §4.6: Named begin-end block for deterministic scoping
// =============================================================================
TEST(ParserSection4, Sec4_6_NamedBeginEndScope) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : seq_blk\n"
      "    x = 1;\n"
      "    y = 2;\n"
      "  end : seq_blk\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "seq_blk");
}

struct ParseResult9c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9c Parse(const std::string& src) {
  ParseResult9c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// LRM section 9.3.1 -- Sequential blocks (additional tests)
// =============================================================================
TEST(ParserSection9, SequentialBlockNamedBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : my_seq\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "  end : my_seq\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->label, "my_seq");
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

struct ParseResult90301 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult90301 Parse(const std::string& src) {
  ParseResult90301 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// 3. Named begin-end block creating a subscope
TEST(ParserClause03, Cl3_13_NamedBeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : my_block\n"
      "    int x;\n"
      "    x = 1;\n"
      "  end : my_block\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1u);
  auto* item = mod->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kInitialBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->label, "my_block");
}

// 4. Nested named begin-end blocks
TEST(ParserClause03, Cl3_13_NestedNamedBlocks) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : outer\n"
      "    begin : inner\n"
      "      int y;\n"
      "      y = 42;\n"
      "    end : inner\n"
      "  end : outer\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->label, "outer");
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->label, "inner");
}

// =============================================================================
// LRM section 12.6 -- Named blocks / block labels
// =============================================================================
TEST(ParserSection12, NamedBeginEnd) {
  auto r = Parse(
      "module t;\n"
      "  initial begin : my_block\n"
      "    x = 1;\n"
      "  end : my_block\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "my_block");
}

// 25. begin-end with no name (anonymous block)
TEST(ParserClause03, Cl3_13_AnonymousBeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = 5;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  // Anonymous blocks have an empty label.
  EXPECT_TRUE(item->body->label.empty());
}

TEST(ParserSection12, NamedBeginEndNoEndLabel) {
  auto r = Parse(
      "module t;\n"
      "  initial begin : blk\n"
      "    x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "blk");
}

// 26. Multiple named blocks at same level
TEST(ParserClause03, Cl3_13_MultipleNamedBlocksSameLevel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    begin : block_a\n"
      "      int x;\n"
      "      x = 1;\n"
      "    end : block_a\n"
      "    begin : block_b\n"
      "      int y;\n"
      "      y = 2;\n"
      "    end : block_b\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->label, "block_a");
  EXPECT_EQ(body->stmts[1]->label, "block_b");
}

struct ParseResult9e {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9e Parse(const std::string& src) {
  ParseResult9e result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* FirstInitialStmt(ParseResult9e& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

// ---------------------------------------------------------------------------
// 5. Named fork-join with matching end labels
// ---------------------------------------------------------------------------
TEST(ParserSection9, Sec9_3_2_NamedForkJoinMatchingLabels) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : thread_group\n"
      "      #10 a = 1;\n"
      "      #20 b = 2;\n"
      "    join : thread_group\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "thread_group");
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoin);
}

TEST(ParserSection12, NamedForkJoin) {
  auto r = Parse(
      "module t;\n"
      "  initial fork : my_fork\n"
      "    x = 1;\n"
      "  join : my_fork\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kFork);
  EXPECT_EQ(body->label, "my_fork");
}

// =============================================================================
// LRM section 9.3.1 -- Sequential blocks (additional)
// Nested blocks with names, and automatic variable lifetime in blocks.
// =============================================================================
TEST(ParserSection9c, NestedNamedSequentialBlocks) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : outer\n"
      "    begin : inner\n"
      "      a = 1;\n"
      "    end : inner\n"
      "  end : outer\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "outer");
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts[0]->label, "inner");
}

}  // namespace
