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

}  // namespace
