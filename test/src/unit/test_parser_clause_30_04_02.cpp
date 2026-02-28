// §30.4.2: Simple module paths

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.7 -- Specify section
// =============================================================================
TEST(ParserAnnexA, A7SpecifyParallelPath) {
  auto r = Parse("module m; specify (a => b) = 5; endspecify endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kSpecifyBlock);
  ASSERT_GE(r.cu->modules[0]->items[0]->specify_items.size(), 1u);
}

ModuleItem* FindSpecifyBlock(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) return item;
  }
  return nullptr;
}

TEST(ParserA701, SpecifyBlockSingleItem) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
}

struct ParseResult31 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult31 Parse(const std::string& src) {
  ParseResult31 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

using ConfigParseTest = ProgramTestParse;

TEST(ParserSection28, Sec28_12_MultiplePathsInSpecifyBlock) {
  auto r = Parse(
      "module m(input a, b, output x, y);\n"
      "  specify\n"
      "    (a => x) = 5;\n"
      "    (b => y) = 7;\n"
      "    (a => y) = 9;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 3u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(spec->specify_items[1]->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(spec->specify_items[2]->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(spec->specify_items[0]->path.path_kind, SpecifyPathKind::kParallel);
  EXPECT_EQ(spec->specify_items[1]->path.path_kind, SpecifyPathKind::kParallel);
  EXPECT_EQ(spec->specify_items[2]->path.path_kind, SpecifyPathKind::kParallel);
}

// =============================================================================
// A.7.3 specify_input_terminal_descriptor — with constant_range_expression
// =============================================================================
// Input terminal with bit-select
TEST(ParserA703, InputTerminalBitSelect) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    (a[3] => b) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* si = GetSolePathItem(r);
  ASSERT_NE(si, nullptr);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0].name, "a");
  EXPECT_EQ(si->path.src_ports[0].range_kind, SpecifyRangeKind::kBitSelect);
  EXPECT_NE(si->path.src_ports[0].range_left, nullptr);
  EXPECT_EQ(si->path.src_ports[0].range_right, nullptr);
}

}  // namespace
