// Tests for A.7.1 — Specify block declaration

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

ModuleItem *FindSpecifyBlock(const std::vector<ModuleItem *> &items) {
  for (auto *item : items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock)
      return item;
  }
  return nullptr;
}

} // namespace

// =============================================================================
// A.7.1 specify_block ::= specify { specify_item } endspecify
// =============================================================================

TEST(ParserA701, SpecifyBlockEmpty) {
  auto r = Parse("module m; specify endspecify endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(spec->kind, ModuleItemKind::kSpecifyBlock);
  EXPECT_EQ(spec->specify_items.size(), 0u);
}

TEST(ParserA701, SpecifyBlockSingleItem) {
  auto r = Parse("module m;\n"
                 "  specify\n"
                 "    (a => b) = 5;\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
}

TEST(ParserA701, SpecifyBlockMultipleItems) {
  auto r = Parse("module m;\n"
                 "  specify\n"
                 "    (a => b) = 5;\n"
                 "    (c => d) = 10;\n"
                 "    $setup(data, posedge clk, 3);\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 3u);
}

// =============================================================================
// A.7.1 specify_item — all 5 alternatives
// =============================================================================

TEST(ParserA701, SpecifyItemSpecparamDecl) {
  auto r = Parse("module m;\n"
                 "  specify\n"
                 "    specparam tPD = 10;\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kSpecparam);
}

TEST(ParserA701, SpecifyItemPulsestyleDecl) {
  auto r = Parse("module m;\n"
                 "  specify\n"
                 "    pulsestyle_onevent out1;\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kPulsestyle);
}

TEST(ParserA701, SpecifyItemShowcancelledDecl) {
  auto r = Parse("module m;\n"
                 "  specify\n"
                 "    showcancelled out1;\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kShowcancelled);
}

TEST(ParserA701, SpecifyItemPathDecl) {
  auto r = Parse("module m;\n"
                 "  specify\n"
                 "    (a => b) = 5;\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kPathDecl);
}

TEST(ParserA701, SpecifyItemSystemTimingCheck) {
  auto r = Parse("module m;\n"
                 "  specify\n"
                 "    $setup(data, posedge clk, 10);\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kTimingCheck);
}

TEST(ParserA701, SpecifyItemAllFiveKinds) {
  auto r = Parse("module m;\n"
                 "  specify\n"
                 "    specparam tPD = 5;\n"
                 "    pulsestyle_onevent out1;\n"
                 "    showcancelled out2;\n"
                 "    (a => b) = tPD;\n"
                 "    $setup(data, posedge clk, 10);\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 5u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kSpecparam);
  EXPECT_EQ(spec->specify_items[1]->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_EQ(spec->specify_items[2]->kind, SpecifyItemKind::kShowcancelled);
  EXPECT_EQ(spec->specify_items[3]->kind, SpecifyItemKind::kPathDecl);
  EXPECT_EQ(spec->specify_items[4]->kind, SpecifyItemKind::kTimingCheck);
}

// =============================================================================
// A.7.1 pulsestyle_declaration
// =============================================================================

TEST(ParserA701, PulsestyleOneventSingleOutput) {
  auto r = Parse("module m;\n"
                 "  specify\n"
                 "    pulsestyle_onevent out1;\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto *item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_FALSE(item->is_ondetect);
  ASSERT_EQ(item->signal_list.size(), 1u);
  EXPECT_EQ(item->signal_list[0], "out1");
}

TEST(ParserA701, PulsestyleOneventMultipleOutputs) {
  auto r = Parse("module m;\n"
                 "  specify\n"
                 "    pulsestyle_onevent out1, out2, out3;\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto *item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_FALSE(item->is_ondetect);
  ASSERT_EQ(item->signal_list.size(), 3u);
  EXPECT_EQ(item->signal_list[0], "out1");
  EXPECT_EQ(item->signal_list[1], "out2");
  EXPECT_EQ(item->signal_list[2], "out3");
}

TEST(ParserA701, PulsestyleOndetectSingleOutput) {
  auto r = Parse("module m;\n"
                 "  specify\n"
                 "    pulsestyle_ondetect q;\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto *item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_TRUE(item->is_ondetect);
  ASSERT_EQ(item->signal_list.size(), 1u);
  EXPECT_EQ(item->signal_list[0], "q");
}

TEST(ParserA701, PulsestyleOndetectMultipleOutputs) {
  auto r = Parse("module m;\n"
                 "  specify\n"
                 "    pulsestyle_ondetect q1, q2;\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto *item = spec->specify_items[0];
  EXPECT_TRUE(item->is_ondetect);
  ASSERT_EQ(item->signal_list.size(), 2u);
  EXPECT_EQ(item->signal_list[0], "q1");
  EXPECT_EQ(item->signal_list[1], "q2");
}

// =============================================================================
// A.7.1 showcancelled_declaration
// =============================================================================

TEST(ParserA701, ShowcancelledSingleOutput) {
  auto r = Parse("module m;\n"
                 "  specify\n"
                 "    showcancelled out1;\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto *item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kShowcancelled);
  EXPECT_FALSE(item->is_noshowcancelled);
  ASSERT_EQ(item->signal_list.size(), 1u);
  EXPECT_EQ(item->signal_list[0], "out1");
}

TEST(ParserA701, ShowcancelledMultipleOutputs) {
  auto r = Parse("module m;\n"
                 "  specify\n"
                 "    showcancelled out1, out2, out3;\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto *item = spec->specify_items[0];
  EXPECT_FALSE(item->is_noshowcancelled);
  ASSERT_EQ(item->signal_list.size(), 3u);
  EXPECT_EQ(item->signal_list[0], "out1");
  EXPECT_EQ(item->signal_list[1], "out2");
  EXPECT_EQ(item->signal_list[2], "out3");
}

TEST(ParserA701, NoshowcancelledSingleOutput) {
  auto r = Parse("module m;\n"
                 "  specify\n"
                 "    noshowcancelled out1;\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto *item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kShowcancelled);
  EXPECT_TRUE(item->is_noshowcancelled);
  ASSERT_EQ(item->signal_list.size(), 1u);
  EXPECT_EQ(item->signal_list[0], "out1");
}

TEST(ParserA701, NoshowcancelledMultipleOutputs) {
  auto r = Parse("module m;\n"
                 "  specify\n"
                 "    noshowcancelled out1, out2;\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto *item = spec->specify_items[0];
  EXPECT_TRUE(item->is_noshowcancelled);
  ASSERT_EQ(item->signal_list.size(), 2u);
  EXPECT_EQ(item->signal_list[0], "out1");
  EXPECT_EQ(item->signal_list[1], "out2");
}

// =============================================================================
// A.7.1 specify_block coexistence with other module items
// =============================================================================

TEST(ParserA701, SpecifyBlockCoexistsWithModuleItems) {
  auto r = Parse("module m;\n"
                 "  logic a;\n"
                 "  specify\n"
                 "    (a => b) = 5;\n"
                 "  endspecify\n"
                 "  assign a = 1;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kSpecifyBlock);
  EXPECT_EQ(items[2]->kind, ModuleItemKind::kContAssign);
}

TEST(ParserA701, MultipleSpecifyBlocksInModule) {
  auto r = Parse("module m;\n"
                 "  specify\n"
                 "    (a => b) = 5;\n"
                 "  endspecify\n"
                 "  specify\n"
                 "    (c => d) = 10;\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &items = r.cu->modules[0]->items;
  int spec_count = 0;
  for (auto *item : items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock)
      ++spec_count;
  }
  EXPECT_EQ(spec_count, 2);
}

// =============================================================================
// A.7.1 pulsestyle and showcancelled together
// =============================================================================

TEST(ParserA701, PulsestyleAndShowcancelledTogether) {
  auto r = Parse("module m;\n"
                 "  specify\n"
                 "    pulsestyle_ondetect out1;\n"
                 "    showcancelled out1;\n"
                 "  endspecify\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 2u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_TRUE(spec->specify_items[0]->is_ondetect);
  EXPECT_EQ(spec->specify_items[1]->kind, SpecifyItemKind::kShowcancelled);
  EXPECT_FALSE(spec->specify_items[1]->is_noshowcancelled);
}
