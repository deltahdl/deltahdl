// §30.7.4.1: On-event versus on-detect pulse filtering

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

ModuleItem* FindSpecifyBlock(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) return item;
  }
  return nullptr;
}

namespace {

TEST(ParserA701, SpecifyItemPulsestyleDecl) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_onevent out1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kPulsestyle);
}

// =============================================================================
// A.7.1 pulsestyle_declaration
// =============================================================================
TEST(ParserA701, PulsestyleOneventSingleOutput) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_onevent out1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto* item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_FALSE(item->is_ondetect);
  ASSERT_EQ(item->signal_list.size(), 1u);
  EXPECT_EQ(item->signal_list[0], "out1");
}

TEST(ParserA701, PulsestyleOneventMultipleOutputs) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_onevent out1, out2, out3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto* item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_FALSE(item->is_ondetect);
  ASSERT_EQ(item->signal_list.size(), 3u);
  EXPECT_EQ(item->signal_list[0], "out1");
  EXPECT_EQ(item->signal_list[1], "out2");
  EXPECT_EQ(item->signal_list[2], "out3");
}

TEST(ParserA701, PulsestyleOndetectSingleOutput) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_ondetect q;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto* item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_TRUE(item->is_ondetect);
  ASSERT_EQ(item->signal_list.size(), 1u);
  EXPECT_EQ(item->signal_list[0], "q");
}

TEST(ParserA701, PulsestyleOndetectMultipleOutputs) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    pulsestyle_ondetect q1, q2;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  auto* item = spec->specify_items[0];
  EXPECT_TRUE(item->is_ondetect);
  ASSERT_EQ(item->signal_list.size(), 2u);
  EXPECT_EQ(item->signal_list[0], "q1");
  EXPECT_EQ(item->signal_list[1], "q2");
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

// =============================================================================
// §30.4 Pulsestyle and showcancelled
// =============================================================================
TEST_F(SpecifyTest, PulsestyleOnevent) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  pulsestyle_onevent out1;\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto* item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_FALSE(item->is_ondetect);
  ASSERT_EQ(item->signal_list.size(), 1u);
  EXPECT_EQ(item->signal_list[0], "out1");
}

TEST_F(SpecifyTest, PulsestyleOndetect) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  pulsestyle_ondetect out1;\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  EXPECT_TRUE(spec->specify_items[0]->is_ondetect);
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
  auto* si = sp.sole_item;
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
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kPulsestyle);
  EXPECT_TRUE(si->is_ondetect);
  ASSERT_EQ(si->signal_list.size(), 2u);
  EXPECT_EQ(si->signal_list[0], "b");
  EXPECT_EQ(si->signal_list[1], "c");
}

}  // namespace
