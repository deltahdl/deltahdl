// Tests for §30.5 — Module path delay specifications

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult30 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult30 Parse(const std::string& src) {
  ParseResult30 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static ModuleItem* FindSpecifyBlock(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) return item;
  }
  return nullptr;
}

static SpecifyItem* GetSoleSpecifyItem(ModuleItem* spec_block) {
  EXPECT_EQ(spec_block->specify_items.size(), 1u);
  if (spec_block->specify_items.empty()) return nullptr;
  return spec_block->specify_items[0];
}

struct SpecifyParseResult {
  ParseResult30 pr;
  ModuleItem* spec_block = nullptr;
  SpecifyItem* sole_item = nullptr;
};

static SpecifyParseResult ParseSpecifySingle(const std::string& src) {
  SpecifyParseResult result;
  result.pr = Parse(src);
  if (result.pr.cu == nullptr) return result;
  result.spec_block = FindSpecifyBlock(result.pr.cu->modules[0]->items);
  if (result.spec_block != nullptr) {
    result.sole_item = GetSoleSpecifyItem(result.spec_block);
  }
  return result;
}

TEST(ParserSection28, Sec28_12_TwoDelayPath) {
  auto sp = ParseSpecifySingle(
      "module m(input a, output b);\n"
      "  specify\n"
      "    (a => b) = (5, 10);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  EXPECT_EQ(sp.sole_item->kind, SpecifyItemKind::kPathDecl);
  ASSERT_EQ(sp.sole_item->path.delays.size(), 2u);
}

TEST(ParserSection28, Sec28_12_ThreeDelayPath) {
  auto sp = ParseSpecifySingle(
      "module m(input a, output b);\n"
      "  specify\n"
      "    (a => b) = (3, 7, 11);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  ASSERT_EQ(sp.sole_item->path.delays.size(), 3u);
}

TEST(ParserSection28, Sec28_12_SixDelayPath) {
  auto sp = ParseSpecifySingle(
      "module m(input a, output b);\n"
      "  specify\n"
      "    (a => b) = (1, 2, 3, 4, 5, 6);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  ASSERT_EQ(sp.sole_item->path.delays.size(), 6u);
}

TEST(ParserSection28, Sec28_12_TwelveDelayPath) {
  auto sp = ParseSpecifySingle(
      "module m(input a, output b);\n"
      "  specify\n"
      "    (a => b) = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  ASSERT_EQ(sp.sole_item->path.delays.size(), 12u);
}

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

TEST(ParserSection28, Sec28_12_SpecparamMinTypMax) {
  EXPECT_TRUE(
      ParseOk("module m(input a, output b);\n"
              "  specify\n"
              "    specparam tPLH = 3:5:7;\n"
              "    (a => b) = tPLH;\n"
              "  endspecify\n"
              "endmodule\n"));
}
