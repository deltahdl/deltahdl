// Tests for §30.7 — Pulsestyle and showcancelled declarations

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
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult30 Parse(const std::string &src) {
  ParseResult30 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static ModuleItem *FindSpecifyBlock(const std::vector<ModuleItem *> &items) {
  for (auto *item : items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) return item;
  }
  return nullptr;
}

static SpecifyItem *GetSoleSpecifyItem(ModuleItem *spec_block) {
  EXPECT_EQ(spec_block->specify_items.size(), 1u);
  if (spec_block->specify_items.empty()) return nullptr;
  return spec_block->specify_items[0];
}

struct SpecifyParseResult {
  ParseResult30 pr;
  ModuleItem *spec_block = nullptr;
  SpecifyItem *sole_item = nullptr;
};

static SpecifyParseResult ParseSpecifySingle(const std::string &src) {
  SpecifyParseResult result;
  result.pr = Parse(src);
  if (result.pr.cu == nullptr) return result;
  result.spec_block = FindSpecifyBlock(result.pr.cu->modules[0]->items);
  if (result.spec_block != nullptr) {
    result.sole_item = GetSoleSpecifyItem(result.spec_block);
  }
  return result;
}

TEST(ParserSection28, Sec28_12_PulsestyleOnevent) {
  auto sp = ParseSpecifySingle(
      "module m(input a, output b);\n"
      "  specify\n"
      "    pulsestyle_onevent b;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto *si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_FALSE(si->is_ondetect);
  ASSERT_EQ(si->signal_list.size(), 1u);
  EXPECT_EQ(si->signal_list[0], "b");
}

TEST(ParserSection28, Sec28_12_PulsestyleOndetect) {
  auto sp = ParseSpecifySingle(
      "module m(input a, output b, c);\n"
      "  specify\n"
      "    pulsestyle_ondetect b, c;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto *si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_TRUE(si->is_ondetect);
  ASSERT_EQ(si->signal_list.size(), 2u);
  EXPECT_EQ(si->signal_list[0], "b");
  EXPECT_EQ(si->signal_list[1], "c");
}

TEST(ParserSection28, Sec28_12_Showcancelled) {
  auto sp = ParseSpecifySingle(
      "module m(input a, output b);\n"
      "  specify\n"
      "    showcancelled b;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto *si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kShowcancelled);
  EXPECT_FALSE(si->is_noshowcancelled);
  ASSERT_EQ(si->signal_list.size(), 1u);
  EXPECT_EQ(si->signal_list[0], "b");
}

TEST(ParserSection28, Sec28_12_Noshowcancelled) {
  auto sp = ParseSpecifySingle(
      "module m(input a, output b, c);\n"
      "  specify\n"
      "    noshowcancelled b, c;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto *si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kShowcancelled);
  EXPECT_TRUE(si->is_noshowcancelled);
  ASSERT_EQ(si->signal_list.size(), 2u);
}

TEST(ParserSection28, Sec28_12_MixedPathsAndTimingChecks) {
  EXPECT_TRUE(
      ParseOk("module m(input a, d, clk, output b);\n"
              "  specify\n"
              "    specparam tPD = 10;\n"
              "    (a => b) = tPD;\n"
              "    $setup(d, posedge clk, 5);\n"
              "    $hold(posedge clk, d, 3);\n"
              "    showcancelled b;\n"
              "    pulsestyle_onevent b;\n"
              "  endspecify\n"
              "endmodule\n"));
}
