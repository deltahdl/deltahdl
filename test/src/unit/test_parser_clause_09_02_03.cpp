// §9.2.3: Final procedures

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
// A.6.2 Production: final_construct
// final_construct ::= final function_statement
// =============================================================================
TEST(ParserA602, FinalConstruct_SingleStmt) {
  auto r = Parse(
      "module m;\n"
      "  final $display(\"done\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kFinalBlock);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
}

TEST(ParserA602, FinalConstruct_BeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  final begin\n"
      "    $display(\"test1\");\n"
      "    $display(\"test2\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kFinalBlock);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

TEST(ParserA602, FinalConstruct_Multiple) {
  auto r = Parse(
      "module m;\n"
      "  final $display(\"a\");\n"
      "  final $display(\"b\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto finals = FindItems(r.cu->modules[0]->items, ModuleItemKind::kFinalBlock);
  EXPECT_EQ(finals.size(), 2u);
}

TEST(ParserA602, Integration_InitialFinalCoexistence) {
  // initial and final blocks coexist
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    $display(\"start\");\n"
      "    a = 0;\n"
      "  end\n"
      "  final begin\n"
      "    $display(\"end\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* init = FindItem(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  auto* fin = FindItem(r.cu->modules[0]->items, ModuleItemKind::kFinalBlock);
  ASSERT_NE(init, nullptr);
  ASSERT_NE(fin, nullptr);
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

// =============================================================================
// LRM section 9.2.3 -- Final procedures
// Final blocks with begin/end and multiple statements.
// =============================================================================
TEST(ParserSection9c, FinalBlockWithBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  final begin\n"
      "    $display(\"cycles: %0d\", count);\n"
      "    $display(\"done\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* final_item = FindItemByKind(r, ModuleItemKind::kFinalBlock);
  ASSERT_NE(final_item, nullptr);
  ASSERT_NE(final_item->body, nullptr);
  EXPECT_EQ(final_item->body->kind, StmtKind::kBlock);
  EXPECT_GE(final_item->body->stmts.size(), 2u);
}

TEST(ParserSection9c, MultipleFinalBlocks) {
  auto r = Parse(
      "module m;\n"
      "  final $display(\"final1\");\n"
      "  final $display(\"final2\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kFinalBlock) ++count;
  }
  EXPECT_EQ(count, 2);
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
// §4.6: Program block with final block
// =============================================================================
TEST(ParserSection4, Sec4_6_ProgramWithFinalBlock) {
  auto r = Parse(
      "program p;\n"
      "  final begin\n"
      "    $display(\"done\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  ASSERT_EQ(r.cu->programs[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->items[0]->kind, ModuleItemKind::kFinalBlock);
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

TEST(ParserSection9, Sec9_3_1_BlockInFinalBlock) {
  auto r = Parse(
      "module m;\n"
      "  final begin\n"
      "    $display(\"sim done\");\n"
      "    $display(\"cycles: %0d\", cnt);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kFinalBlock) {
      found = true;
      ASSERT_NE(item->body, nullptr);
      EXPECT_EQ(item->body->kind, StmtKind::kBlock);
      EXPECT_GE(item->body->stmts.size(), 2u);
    }
  }
  EXPECT_TRUE(found);
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

// =============================================================================
// §24.12 Program with final block
// =============================================================================
TEST_F(ProgramTestParse, ProgramWithFinalBlock) {
  auto* unit = Parse(
      "program p;\n"
      "  final begin\n"
      "    $display(\"done\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_EQ(unit->programs.size(), 1u);
  ASSERT_EQ(unit->programs[0]->items.size(), 1u);
  EXPECT_EQ(unit->programs[0]->items[0]->kind, ModuleItemKind::kFinalBlock);
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

TEST(ParserSection9b, StructuredProcFinalBlock) {
  auto r = Parse(
      "module m;\n"
      "  final $display(\"done\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kFinalBlock);
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

static ModuleItem* FirstItem(ParseResult4c& r) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.empty())
    return nullptr;
  return r.cu->modules[0]->items[0];
}

// ---------------------------------------------------------------------------
// 23. final block
// ---------------------------------------------------------------------------
TEST(ParserSection4, Sec4_5_FinalBlock) {
  auto r = Parse(
      "module m;\n"
      "  final begin\n"
      "    $display(\"simulation done\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFinalBlock);
  ASSERT_NE(item->body, nullptr);
}

TEST(ParserSection9, FinalBlock) {
  auto r = Parse(
      "module m;\n"
      "  final $display(\"done\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  bool found = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kFinalBlock) {
      found = true;
      ASSERT_NE(item->body, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
