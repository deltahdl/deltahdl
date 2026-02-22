// Tests for §31.6 — Timing check notifier and edge arguments

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult31 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult31 Parse(const std::string &src) {
  ParseResult31 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem *FindSpecifyBlock(const std::vector<ModuleItem *> &items) {
  for (auto *item : items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock)
      return item;
  }
  return nullptr;
}

static SpecifyItem *GetSoleSpecifyItem(ModuleItem *spec_block) {
  EXPECT_EQ(spec_block->specify_items.size(), 1u);
  if (spec_block->specify_items.empty())
    return nullptr;
  return spec_block->specify_items[0];
}

struct SpecifyParseResult {
  ParseResult31 pr;
  ModuleItem *spec_block = nullptr;
  SpecifyItem *sole_item = nullptr;
};

static SpecifyParseResult ParseSpecifySingle(const std::string &src) {
  SpecifyParseResult result;
  result.pr = Parse(src);
  if (result.pr.cu == nullptr)
    return result;
  result.spec_block = FindSpecifyBlock(result.pr.cu->modules[0]->items);
  if (result.spec_block != nullptr) {
    result.sole_item = GetSoleSpecifyItem(result.spec_block);
  }
  return result;
}

TEST(ParserSection28, Sec28_12_TimingCheckWithNotifier) {
  auto sp = ParseSpecifySingle("module m(input d, clk);\n"
                               "  reg notif_reg;\n"
                               "  specify\n"
                               "    $setup(d, posedge clk, 10, notif_reg);\n"
                               "  endspecify\n"
                               "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  EXPECT_EQ(sp.sole_item->timing_check.check_kind, TimingCheckKind::kSetup);
  EXPECT_EQ(sp.sole_item->timing_check.notifier, "notif_reg");
}

TEST(ParserSection28, Sec28_12_TimingCheckWithEdges) {
  auto sp = ParseSpecifySingle("module m(input d, clk);\n"
                               "  specify\n"
                               "    $setup(negedge d, posedge clk, 8);\n"
                               "  endspecify\n"
                               "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto *si = sp.sole_item;
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kSetup);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "d");
  EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.data_terminal.name, "clk");
}
