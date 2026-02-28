// Non-LRM tests

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

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

ParseResult ParseLibrary(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.ParseLibraryText();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

TEST_F(SpecifyTest, NegedgePath) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  (negedge clk => q) = 8;\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(spec->specify_items[0]->path.edge, SpecifyEdge::kNegedge);
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

TEST_F(SpecifyTest, PathDelayWithRiseFall) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  (a => b) = (3, 5);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto& delays = spec->specify_items[0]->path.delays;
  EXPECT_EQ(delays.size(), 2u);
}

TEST_F(SpecifyTest, PathDelayThreeValues) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  (a => b) = (2, 3, 4);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items[0]->path.delays.size(), 3u);
}

// =============================================================================
// §30.3.3 Conditional path delays
// =============================================================================
TEST_F(SpecifyTest, ConditionalIfPath) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  if (sel) (a => b) = 5;\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto* path = spec->specify_items[0];
  EXPECT_EQ(path->kind, SpecifyItemKind::kPathDecl);
  EXPECT_NE(path->path.condition, nullptr);
  EXPECT_FALSE(path->path.is_ifnone);
}

TEST_F(SpecifyTest, IfnoneConditionalPath) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  ifnone (a => b) = 7;\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_TRUE(spec->specify_items[0]->path.is_ifnone);
  EXPECT_EQ(spec->specify_items[0]->path.condition, nullptr);
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
  auto* si = sp.sole_item;
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
  auto* si = sp.sole_item;
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

TEST_F(SpecifyTest, Showcancelled) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  showcancelled out1;\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  auto* item = spec->specify_items[0];
  EXPECT_EQ(item->kind, SpecifyItemKind::kShowcancelled);
  EXPECT_FALSE(item->is_noshowcancelled);
}

TEST_F(SpecifyTest, Noshowcancelled) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  noshowcancelled out1;\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  EXPECT_TRUE(spec->specify_items[0]->is_noshowcancelled);
}

TEST(ParserSection28, Sec28_12_TimingCheckSetup) {
  auto sp = ParseSpecifySingle(
      "module m(input d, clk);\n"
      "  specify\n"
      "    $setup(d, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kTimingCheck);
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kSetup);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kNone);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "d");
  EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.data_terminal.name, "clk");
  ASSERT_EQ(si->timing_check.limits.size(), 1u);
}

TEST(ParserSection28, Sec28_12_TimingCheckHold) {
  auto sp = ParseSpecifySingle(
      "module m(input d, clk);\n"
      "  specify\n"
      "    $hold(posedge clk, d, 5);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kTimingCheck);
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kHold);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "clk");
  EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kNone);
  EXPECT_EQ(si->timing_check.data_terminal.name, "d");
  ASSERT_EQ(si->timing_check.limits.size(), 1u);
}

TEST(ParserSection28, Sec28_12_TimingCheckSetuphold) {
  auto sp = ParseSpecifySingle(
      "module m(input d, clk);\n"
      "  specify\n"
      "    $setuphold(posedge clk, d, 3, 2);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kTimingCheck);
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kSetuphold);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "clk");
  EXPECT_EQ(si->timing_check.data_terminal.name, "d");
  ASSERT_EQ(si->timing_check.limits.size(), 2u);
}

TEST(ParserSection28, Sec28_12_TimingCheckRecovery) {
  auto sp = ParseSpecifySingle(
      "module m(input rst, clk);\n"
      "  specify\n"
      "    $recovery(posedge clk, rst, 6);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kRecovery);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "clk");
  EXPECT_EQ(si->timing_check.data_terminal.name, "rst");
}

TEST(ParserSection28, Sec28_12_TimingCheckRemoval) {
  auto sp = ParseSpecifySingle(
      "module m(input rst, clk);\n"
      "  specify\n"
      "    $removal(negedge rst, posedge clk, 4);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kRemoval);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "rst");
  EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.data_terminal.name, "clk");
}

TEST(ParserSection28, Sec28_12_TimingCheckRecrem) {
  auto sp = ParseSpecifySingle(
      "module m(input rst, clk);\n"
      "  specify\n"
      "    $recrem(posedge clk, rst, 5, 3);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kRecrem);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "clk");
  EXPECT_EQ(si->timing_check.data_terminal.name, "rst");
  ASSERT_EQ(si->timing_check.limits.size(), 2u);
}

TEST(ParserSection28, Sec28_12_MultipleTimingChecksInSpecifyBlock) {
  auto r = Parse(
      "module m(input d, clk, rst);\n"
      "  specify\n"
      "    $setup(d, posedge clk, 5);\n"
      "    $hold(posedge clk, d, 3);\n"
      "    $recovery(posedge clk, rst, 10);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 3u);
  EXPECT_EQ(spec->specify_items[0]->timing_check.check_kind,
            TimingCheckKind::kSetup);
  EXPECT_EQ(spec->specify_items[1]->timing_check.check_kind,
            TimingCheckKind::kHold);
  EXPECT_EQ(spec->specify_items[2]->timing_check.check_kind,
            TimingCheckKind::kRecovery);
}

TEST_F(SpecifyTest, SetupholdTimingCheck) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, 10, 5);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kSetuphold);
  ASSERT_GE(tc.limits.size(), 2u);
}

TEST_F(SpecifyTest, RecremTimingCheck) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $recrem(posedge clk, rst, 8, 3);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kRecrem);
  ASSERT_GE(tc.limits.size(), 2u);
}

TEST(ParserSection28, Sec28_12_TimingCheckWidth) {
  auto sp = ParseSpecifySingle(
      "module m(input clk);\n"
      "  specify\n"
      "    $width(posedge clk, 50);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kWidth);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "clk");
  ASSERT_EQ(si->timing_check.limits.size(), 1u);
}

TEST(ParserSection28, Sec28_12_TimingCheckPeriod) {
  auto sp = ParseSpecifySingle(
      "module m(input clk);\n"
      "  specify\n"
      "    $period(posedge clk, 100);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kPeriod);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "clk");
}

TEST(ParserSection28, Sec28_12_TimingCheckSkew) {
  auto sp = ParseSpecifySingle(
      "module m(input clk1, clk2);\n"
      "  specify\n"
      "    $skew(posedge clk1, posedge clk2, 20);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kSkew);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "clk1");
  EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.data_terminal.name, "clk2");
}

TEST_F(SpecifyTest, WidthTimingCheck) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $width(posedge clk, 20);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kWidth);
  EXPECT_EQ(tc.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc.ref_terminal.name, "clk");
  ASSERT_GE(tc.limits.size(), 1u);
}

TEST_F(SpecifyTest, TimeskewTimingCheck) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $timeskew(posedge clk1, posedge clk2, 5);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kTimeskew);
  EXPECT_EQ(tc.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc.ref_terminal.name, "clk1");
  EXPECT_EQ(tc.data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc.data_terminal.name, "clk2");
  ASSERT_EQ(tc.limits.size(), 1u);
}

TEST_F(SpecifyTest, FullskewTimingCheck) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $fullskew(posedge clk1, negedge clk2, 4, 6);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kFullskew);
  EXPECT_EQ(tc.ref_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc.data_edge, SpecifyEdge::kNegedge);
  ASSERT_GE(tc.limits.size(), 2u);
}

TEST(ParserSection28, Sec28_12_TimingCheckWithNotifier) {
  auto sp = ParseSpecifySingle(
      "module m(input d, clk);\n"
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
  auto sp = ParseSpecifySingle(
      "module m(input d, clk);\n"
      "  specify\n"
      "    $setup(negedge d, posedge clk, 8);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kSetup);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "d");
  EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.data_terminal.name, "clk");
}

TEST_F(SpecifyTest, TimingCheckWithNotifier) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk, 10, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  EXPECT_EQ(spec->specify_items[0]->timing_check.notifier, "ntfr");
}

TEST_F(SpecifyTest, TimeskewWithNotifier) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $timeskew(posedge clk1, posedge clk2, 5, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kTimeskew);
  EXPECT_EQ(tc.notifier, "ntfr");
}

// =============================================================================
// §31.7 Conditioned events
// =============================================================================
TEST_F(SpecifyTest, ConditionedSetup) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& clr, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kSetup);
  EXPECT_EQ(tc.ref_terminal.name, "data");
  EXPECT_NE(tc.ref_condition, nullptr);
}

TEST_F(SpecifyTest, ConditionedHoldBothSignals) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk &&& en, data &&& reset, 5);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kHold);
  EXPECT_NE(tc.ref_condition, nullptr);
  EXPECT_NE(tc.data_condition, nullptr);
}

// =============================================================================
// §31.9 Extended $setuphold arguments
// =============================================================================
TEST_F(SpecifyTest, SetupholdWithDelayedSignals) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $setuphold(posedge clk, data, -10, 20, ntfr, , , dCLK, dD);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kSetuphold);
  EXPECT_EQ(tc.notifier, "ntfr");
  EXPECT_EQ(tc.delayed_ref, "dCLK");
  EXPECT_EQ(tc.delayed_data, "dD");
}

// =============================================================================
// §33 Configuration declarations
// =============================================================================
TEST_F(ConfigParseTest, BasicConfig) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  EXPECT_EQ(unit->configs[0]->name, "cfg");
}

TEST_F(ConfigParseTest, ConfigWithEndLabel) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
    endconfig : cfg
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  EXPECT_EQ(unit->configs[0]->name, "cfg");
}

TEST_F(ConfigParseTest, ConfigWithDefaultClause) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
      default liblist lib1 lib2;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  EXPECT_EQ(unit->configs[0]->name, "cfg");
}

TEST_F(ConfigParseTest, ConfigWithInstanceClause) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
      instance top.u1 liblist lib2;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  EXPECT_EQ(unit->configs[0]->name, "cfg");
}

TEST_F(ConfigParseTest, ConfigWithCellClause) {
  auto* unit = Parse(R"(
    config cfg;
      design lib.top;
      cell top use lib.other;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 1u);
  EXPECT_EQ(unit->configs[0]->name, "cfg");
}

TEST_F(ConfigParseTest, ConfigCoexistsWithModule) {
  auto* unit = Parse(R"(
    module m;
    endmodule
    config cfg;
      design lib.top;
    endconfig
  )");
  EXPECT_EQ(unit->modules.size(), 1u);
  EXPECT_EQ(unit->configs.size(), 1u);
  EXPECT_EQ(unit->configs[0]->name, "cfg");
}

TEST_F(ConfigParseTest, MultipleConfigs) {
  auto* unit = Parse(R"(
    config cfg1;
      design lib.top1;
    endconfig
    config cfg2;
      design lib.top2;
    endconfig
  )");
  ASSERT_EQ(unit->configs.size(), 2u);
  EXPECT_EQ(unit->configs[0]->name, "cfg1");
  EXPECT_EQ(unit->configs[1]->name, "cfg2");
}

// =============================================================================
// A.1.1 library_text ::= { library_description }
// =============================================================================
// Empty library text produces an empty CompilationUnit.
TEST(LibraryText, EmptyInput) {
  auto r = ParseLibrary("");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->libraries.empty());
  EXPECT_TRUE(r.cu->lib_includes.empty());
  EXPECT_TRUE(r.cu->configs.empty());
}

// A null library description (bare semicolon) is valid.
TEST(LibraryText, NullDescription) {
  auto r = ParseLibrary(";\n;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->libraries.empty());
}

// =============================================================================
// A.1.1 library_declaration ::=
//   library library_identifier file_path_spec
//   { , file_path_spec } [ -incdir file_path_spec { , file_path_spec } ] ;
// =============================================================================
// Basic library declaration with a single file path.
TEST(LibraryText, BasicLibraryDecl) {
  auto r = ParseLibrary("library mylib /proj/rtl/top.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->name, "mylib");
  ASSERT_EQ(r.cu->libraries[0]->file_paths.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "/proj/rtl/top.v");
}

// Library declaration with wildcard file path.
TEST(LibraryText, LibraryDeclWildcard) {
  auto r = ParseLibrary("library rtlLib *.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->name, "rtlLib");
  ASSERT_EQ(r.cu->libraries[0]->file_paths.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "*.v");
}

// Library declaration with dot-slash relative path.
TEST(LibraryText, LibraryDeclDotSlash) {
  auto r = ParseLibrary("library gateLib ./*.vg;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "./*.vg");
}

// Library declaration with multiple file paths.
TEST(LibraryText, LibraryDeclMultiplePaths) {
  auto r = ParseLibrary("library lib /a/*.v, /b/*.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  ASSERT_EQ(r.cu->libraries[0]->file_paths.size(), 2u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "/a/*.v");
  EXPECT_EQ(r.cu->libraries[0]->file_paths[1], "/b/*.v");
}

// Library declaration with -incdir clause.
TEST(LibraryText, LibraryDeclWithIncdir) {
  auto r = ParseLibrary("library lib /proj/*.v -incdir /proj/inc;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  ASSERT_EQ(r.cu->libraries[0]->file_paths.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "/proj/*.v");
  ASSERT_EQ(r.cu->libraries[0]->incdir_paths.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->incdir_paths[0], "/proj/inc");
}

// Library declaration with multiple -incdir paths.
TEST(LibraryText, LibraryDeclMultipleIncdir) {
  auto r = ParseLibrary("library lib /proj/*.v -incdir /inc1, /inc2, /inc3;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  ASSERT_EQ(r.cu->libraries[0]->incdir_paths.size(), 3u);
  EXPECT_EQ(r.cu->libraries[0]->incdir_paths[0], "/inc1");
  EXPECT_EQ(r.cu->libraries[0]->incdir_paths[1], "/inc2");
  EXPECT_EQ(r.cu->libraries[0]->incdir_paths[2], "/inc3");
}

// Library declaration with both multiple file paths and multiple -incdir.
TEST(LibraryText, LibraryDeclFullForm) {
  auto r = ParseLibrary(
      "library rtlLib /proj/rtl/*.v, /proj/extra/*.v\n"
      "  -incdir /proj/inc, /proj/common;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->name, "rtlLib");
  ASSERT_EQ(r.cu->libraries[0]->file_paths.size(), 2u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "/proj/rtl/*.v");
  EXPECT_EQ(r.cu->libraries[0]->file_paths[1], "/proj/extra/*.v");
  ASSERT_EQ(r.cu->libraries[0]->incdir_paths.size(), 2u);
  EXPECT_EQ(r.cu->libraries[0]->incdir_paths[0], "/proj/inc");
  EXPECT_EQ(r.cu->libraries[0]->incdir_paths[1], "/proj/common");
}

// Library declaration with hierarchical wildcard path (...).
TEST(LibraryText, LibraryDeclHierarchicalWildcard) {
  auto r = ParseLibrary("library deepLib .../a.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], ".../a.v");
}

// Library declaration with single-char wildcard (?).
TEST(LibraryText, LibraryDeclQuestionWildcard) {
  auto r = ParseLibrary("library lib ./rtl/?.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "./rtl/?.v");
}

// Library declaration with directory-only path (trailing slash).
TEST(LibraryText, LibraryDeclDirectoryPath) {
  auto r = ParseLibrary("library lib /proj/rtl/;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->file_paths[0], "/proj/rtl/");
}

}  // namespace
