// Tests for §30.4 — Module path declarations

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

static bool HasFullPathDecl(ModuleItem* spec_block) {
  for (auto* si : spec_block->specify_items) {
    if (si->kind == SpecifyItemKind::kPathDecl &&
        si->path.path_kind == SpecifyPathKind::kFull) {
      return true;
    }
  }
  return false;
}

static bool HasSpecifyItemKind(ModuleItem* spec_block, SpecifyItemKind kind) {
  for (auto* si : spec_block->specify_items) {
    if (si->kind == kind) return true;
  }
  return false;
}

TEST(ParserSection28, SpecifyBlockSimplePath) {
  auto r = Parse(
      "module m(input a, output b);\n"
      "  specify\n"
      "    (a => b) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_GE(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(spec->specify_items[0]->path.path_kind, SpecifyPathKind::kParallel);
}

TEST(ParserSection28, SpecifyBlockFullPath) {
  auto r = Parse(
      "module m(input a, b, output c);\n"
      "  specify\n"
      "    (a, b *> c) = (5, 10);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  EXPECT_TRUE(HasFullPathDecl(spec));
}

TEST(ParserSection28, SpecifyBlockWithSpecparam) {
  auto r = Parse(
      "module m(input clk, output q);\n"
      "  specify\n"
      "    specparam tDelay = 10;\n"
      "    (clk => q) = tDelay;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  EXPECT_TRUE(HasSpecifyItemKind(spec, SpecifyItemKind::kSpecparam));
  EXPECT_TRUE(HasSpecifyItemKind(spec, SpecifyItemKind::kPathDecl));
}

TEST(ParserSection28, Sec28_12_ConditionalPath) {
  auto sp = ParseSpecifySingle(
      "module m(input a, en, output b);\n"
      "  specify\n"
      "    if (en) (a => b) = 10;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
  EXPECT_NE(si->path.condition, nullptr);
  EXPECT_FALSE(si->path.is_ifnone);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0], "a");
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  EXPECT_EQ(si->path.dst_ports[0], "b");
  ASSERT_EQ(si->path.delays.size(), 1u);
}

TEST(ParserSection28, Sec28_12_IfnonePath) {
  auto sp = ParseSpecifySingle(
      "module m(input a, output b);\n"
      "  specify\n"
      "    ifnone (a => b) = 15;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  EXPECT_TRUE(si->path.is_ifnone);
  EXPECT_EQ(si->path.condition, nullptr);
  ASSERT_EQ(si->path.delays.size(), 1u);
}

TEST(ParserSection28, Sec28_12_PosedgeSensitivePath) {
  auto sp = ParseSpecifySingle(
      "module m(input clk, output q);\n"
      "  specify\n"
      "    (posedge clk => q) = 5;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kParallel);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0], "clk");
  ASSERT_EQ(si->path.dst_ports.size(), 1u);
  EXPECT_EQ(si->path.dst_ports[0], "q");
}

TEST(ParserSection28, Sec28_12_NegedgeSensitivePath) {
  auto sp = ParseSpecifySingle(
      "module m(input clk, output q);\n"
      "  specify\n"
      "    (negedge clk => q) = 8;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(si->path.edge, SpecifyEdge::kNegedge);
  ASSERT_EQ(si->path.src_ports.size(), 1u);
  EXPECT_EQ(si->path.src_ports[0], "clk");
}

TEST(ParserSection28, Sec28_12_MultipleSourceDestPorts) {
  auto sp = ParseSpecifySingle(
      "module m(input a, b, c, output x, y);\n"
      "  specify\n"
      "    (a, b, c *> x, y) = 12;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(si->path.path_kind, SpecifyPathKind::kFull);
  ASSERT_EQ(si->path.src_ports.size(), 3u);
  EXPECT_EQ(si->path.src_ports[0], "a");
  EXPECT_EQ(si->path.src_ports[1], "b");
  EXPECT_EQ(si->path.src_ports[2], "c");
  ASSERT_EQ(si->path.dst_ports.size(), 2u);
  EXPECT_EQ(si->path.dst_ports[0], "x");
  EXPECT_EQ(si->path.dst_ports[1], "y");
}

TEST(ParserSection28, Sec28_12_PosedgeFullPath) {
  EXPECT_TRUE(
      ParseOk("module m(input clk, output q, qb);\n"
              "  specify\n"
              "    (posedge clk *> q, qb) = (3, 5);\n"
              "  endspecify\n"
              "endmodule\n"));
}

TEST(ParserSection28, Sec28_12_ConditionalFullPath) {
  EXPECT_TRUE(
      ParseOk("module m(input a, b, en, output y);\n"
              "  specify\n"
              "    if (en) (a, b *> y) = 10;\n"
              "  endspecify\n"
              "endmodule\n"));
}
