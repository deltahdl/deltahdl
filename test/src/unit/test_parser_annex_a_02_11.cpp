#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string& src) {
  ParseResult result;
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

static ModuleItem* FindItemByKind(const std::vector<ModuleItem*>& items,
                                  ModuleItemKind kind) {
  for (auto* item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

// =============================================================================
// §A.2.11 Production #1: covergroup_declaration
// =============================================================================

TEST(ParserA211, CovergroupDecl_Basic) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCovergroupDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kCovergroupDecl);
  EXPECT_EQ(item->name, "cg");
  EXPECT_TRUE(item->loc.IsValid());
}

TEST(ParserA211, CovergroupDecl_WithClockingEvent) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg @(posedge clk);\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CovergroupDecl_WithPortList) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg(ref int x, input bit [3:0] y);\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CovergroupDecl_WithEmptyPortList) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg();\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CovergroupDecl_WithPortsAndEvent) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg(ref int x) @(posedge clk);\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CovergroupDecl_WithSampleFunction) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg with function sample(int x, bit y);\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CovergroupDecl_WithBlockEvent) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg @@(begin test_phase or end test_phase);\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CovergroupDecl_WithExtends) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup child extends parent;\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CovergroupDecl_WithEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "  endgroup : cg\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCovergroupDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "cg");
}

TEST(ParserA211, CovergroupDecl_InClass) {
  EXPECT_TRUE(ParseOk(
      "class c;\n"
      "  covergroup cg;\n"
      "  endgroup\n"
      "endclass\n"));
}

// =============================================================================
// §A.2.11 Production #2: coverage_spec_or_option
// =============================================================================

TEST(ParserA211, CoverageSpecOrOption_Option) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    option.auto_bin_max = 128;\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverageSpecOrOption_CoverSpec) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #3: coverage_option
// =============================================================================

TEST(ParserA211, CoverageOption_OptionMember) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    option.weight = 2;\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverageOption_TypeOption) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    type_option.weight = 3;\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverageOption_AutoBinMax) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    option.auto_bin_max = 64;\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverageOption_Goal) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    option.goal = 90;\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #4: coverage_spec
// =============================================================================

TEST(ParserA211, CoverageSpec_CoverPoint) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint addr;\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverageSpec_CoverCross) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2;\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #5: coverage_event
// =============================================================================

TEST(ParserA211, CoverageEvent_ClockingEvent) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverageEvent_NegedgeClocking) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg @(negedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverageEvent_WithFunctionSample) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg with function sample(bit [3:0] val);\n"
      "    coverpoint val;\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverageEvent_BlockEventBegin) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg @@(begin test_phase);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverageEvent_BlockEventEnd) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg @@(end test_phase);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #6: block_event_expression
// =============================================================================

TEST(ParserA211, BlockEventExpression_BeginHierarchical) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg @@(begin top.test.run_phase);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, BlockEventExpression_Or) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg @@(begin phase1 or end phase2);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, BlockEventExpression_MultipleOr) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg @@(begin a or begin b or end c);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #7: hierarchical_btf_identifier
// =============================================================================

TEST(ParserA211, HierarchicalBtfIdentifier_Simple) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg @@(begin my_task);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, HierarchicalBtfIdentifier_Dotted) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg @@(begin top.dut.task1);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #8: cover_point
// =============================================================================

TEST(ParserA211, CoverPoint_BasicExpression) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverPoint_Labeled) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint addr;\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverPoint_WithDataType) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint x {\n"
      "      bins low = {[0:3]};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverPoint_WithIff) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint addr iff (enable);\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverPoint_WithBinsBlock) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins a = {0, 1};\n"
      "      bins b = {2, 3};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverPoint_LabeledWithIff) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    my_cp: coverpoint data iff (valid);\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverPoint_ComplexExpression) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint (a + b);\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #9: bins_or_empty
// =============================================================================

TEST(ParserA211, BinsOrEmpty_Semicolon) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, BinsOrEmpty_WithBraces) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins a = {1};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, BinsOrEmpty_EmptyBraces) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {}\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #10: bins_or_options
// =============================================================================

TEST(ParserA211, BinsOrOptions_ValueRangeList) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins low = {[0:3]};\n"
      "      bins mid = {[4:7]};\n"
      "      bins high = {[8:15]};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, BinsOrOptions_WithArraySize) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins b[4] = {[0:15]};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, BinsOrOptions_AutoSizedArray) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins b[] = {[0:15]};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, BinsOrOptions_WildcardBins) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      wildcard bins even = {4'b???0};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, BinsOrOptions_WithIff) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins b = {[0:3]} iff (enable);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, BinsOrOptions_Default) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins others = default;\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, BinsOrOptions_DefaultSequence) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins others = default sequence;\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, BinsOrOptions_SetCovergroupExpr) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins b = x;\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, BinsOrOptions_WithWithClause) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins b = {[0:15]} with (item > 5);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #11: bins_keyword
// =============================================================================

TEST(ParserA211, BinsKeyword_Bins) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins a = {0};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, BinsKeyword_IllegalBins) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      illegal_bins bad = {255};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, BinsKeyword_IgnoreBins) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      ignore_bins skip = {128};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #12: trans_list
// =============================================================================

TEST(ParserA211, TransList_Single) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins t = (1 => 2);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, TransList_Multiple) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins t = (1 => 2), (3 => 4);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #13: trans_set
// =============================================================================

TEST(ParserA211, TransSet_SingleRange) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins t = (1 => 3);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, TransSet_MultipleRanges) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins t = (1 => 3 => 5);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #14: trans_range_list
// =============================================================================

TEST(ParserA211, TransRangeList_SimpleItem) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins t = (0 => 1);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, TransRangeList_ConsecutiveRepeat) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins t = (1 [* 3]);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, TransRangeList_GotoRepeat) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins t = (1 [-> 3]);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, TransRangeList_NonConsecutiveRepeat) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins t = (1 [= 3]);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #15: trans_item (alias for covergroup_range_list)
// =============================================================================

TEST(ParserA211, TransItem_SingleValue) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins t = (5 => 10);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, TransItem_MultipleValues) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins t = (1, 2, 3 => 4, 5);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #16: repeat_range
// =============================================================================

TEST(ParserA211, RepeatRange_SingleExpr) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins t = (1 [* 5]);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, RepeatRange_Range) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins t = (1 [* 2:5]);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #17: cover_cross
// =============================================================================

TEST(ParserA211, CoverCross_Basic) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2;\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverCross_Labeled) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    my_cross: cross cp1, cp2;\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverCross_WithIff) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2 iff (enable);\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverCross_WithBody) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2 {\n"
      "      bins sel = binsof(cp1) intersect {[0:3]};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #18: list_of_cross_items
// =============================================================================

TEST(ParserA211, ListOfCrossItems_Two) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2;\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, ListOfCrossItems_Three) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cp3: coverpoint c;\n"
      "    cross cp1, cp2, cp3;\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #19: cross_item
// =============================================================================

TEST(ParserA211, CrossItem_CoverPointIdentifier) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp_a: coverpoint a;\n"
      "    cp_b: coverpoint b;\n"
      "    cross cp_a, cp_b;\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #20: cross_body
// =============================================================================

TEST(ParserA211, CrossBody_Empty) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2;\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CrossBody_WithItems) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2 {\n"
      "      bins sel = binsof(cp1);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #21: cross_body_item
// =============================================================================

TEST(ParserA211, CrossBodyItem_BinsSelection) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2 {\n"
      "      bins ab = binsof(cp1) intersect {[0:3]};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CrossBodyItem_FunctionDecl) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2 {\n"
      "      function CrossQueueType myFunc(int val);\n"
      "        return '{val};\n"
      "      endfunction\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #22: bins_selection_or_option
// =============================================================================

TEST(ParserA211, BinsSelectionOrOption_CoverageOption) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2 {\n"
      "      option.weight = 5;\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, BinsSelectionOrOption_BinsSelection) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2 {\n"
      "      bins selected = binsof(cp1);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #23: bins_selection
// =============================================================================

TEST(ParserA211, BinsSelection_Basic) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2 {\n"
      "      bins my_bin = binsof(cp1);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, BinsSelection_WithIff) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2 {\n"
      "      bins sel = binsof(cp1) iff (enable);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #24: select_expression
// =============================================================================

TEST(ParserA211, SelectExpression_SelectCondition) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2 {\n"
      "      bins sel = binsof(cp1);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, SelectExpression_Negated) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2 {\n"
      "      bins sel = !binsof(cp1);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, SelectExpression_And) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2 {\n"
      "      bins sel = binsof(cp1) && binsof(cp2);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, SelectExpression_Or) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2 {\n"
      "      bins sel = binsof(cp1) || binsof(cp2);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, SelectExpression_Parenthesized) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2 {\n"
      "      bins sel = (binsof(cp1) && binsof(cp2));\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #25: select_condition
// =============================================================================

TEST(ParserA211, SelectCondition_Binsof) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2 {\n"
      "      bins sel = binsof(cp1);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, SelectCondition_BinsofIntersect) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2 {\n"
      "      bins sel = binsof(cp1) intersect {[0:3]};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #26: bins_expression
// =============================================================================

TEST(ParserA211, BinsExpression_Variable) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2 {\n"
      "      bins sel = binsof(cp1);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, BinsExpression_CoverPointDotBin) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2 {\n"
      "      bins sel = binsof(cp1.low);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #27: covergroup_range_list
// =============================================================================

TEST(ParserA211, CovergroupRangeList_Single) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins a = {5};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CovergroupRangeList_Multiple) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins a = {1, 2, 3, 4, 5};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CovergroupRangeList_MixedRanges) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins a = {1, [3:5], 8, [10:15]};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #28: covergroup_value_range
// =============================================================================

TEST(ParserA211, CovergroupValueRange_SingleValue) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins a = {42};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CovergroupValueRange_ClosedRange) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins a = {[0:255]};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CovergroupValueRange_OpenLow) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins a = {[$:100]};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CovergroupValueRange_OpenHigh) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins a = {[100:$]};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #29: with_covergroup_expression
// =============================================================================

TEST(ParserA211, WithCovergroupExpression) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins b = {[0:255]} with (item > 10);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #30: set_covergroup_expression
// =============================================================================

TEST(ParserA211, SetCovergroupExpression) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins b = x;\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #31: integer_covergroup_expression
// =============================================================================

TEST(ParserA211, IntegerCovergroupExpression_Expr) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins b[4] = {[0:15]};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #32: cross_set_expression
// =============================================================================

TEST(ParserA211, CrossSetExpression) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2 {\n"
      "      bins sel = binsof(cp1) intersect {[0:7]};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #33: covergroup_expression
// =============================================================================

TEST(ParserA211, CovergroupExpression_Literal) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins a = {10};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CovergroupExpression_BinaryOp) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins a = {a + b};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

// =============================================================================
// Additional comprehensive tests
// =============================================================================

TEST(ParserA211, FullCovergroup_MultipleElements) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg @(posedge clk);\n"
      "    option.auto_bin_max = 64;\n"
      "    cp_addr: coverpoint addr {\n"
      "      bins low = {[0:63]};\n"
      "      bins mid = {[64:191]};\n"
      "      bins high = {[192:255]};\n"
      "    }\n"
      "    cp_data: coverpoint data;\n"
      "    cross cp_addr, cp_data;\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverGroup_AllBinTypes) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins a = {0, 1, 2};\n"
      "      bins b[3] = {[0:8]};\n"
      "      bins c[] = {[0:15]};\n"
      "      bins d = default;\n"
      "      bins e = default sequence;\n"
      "      wildcard bins w = {4'b1??0};\n"
      "      illegal_bins bad = {255};\n"
      "      ignore_bins skip = {128};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverGroup_TransitionBins) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins t1 = (0 => 1 => 2);\n"
      "      bins t2 = (0 => 1), (2 => 3);\n"
      "      bins t3 = (1 [* 3]);\n"
      "      bins t4 = (1 [-> 2]);\n"
      "      bins t5 = (1 [= 2]);\n"
      "      bins t6 = (1 [* 2:5]);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverGroup_CrossWithBinsSelection) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2 {\n"
      "      bins sel1 = binsof(cp1) intersect {[0:3]};\n"
      "      bins sel2 = !binsof(cp2);\n"
      "      bins sel3 = binsof(cp1) && binsof(cp2);\n"
      "      ignore_bins ig = binsof(cp1) intersect {255};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverGroup_MultipleCoverpoints) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg @(posedge clk);\n"
      "    type_option.weight = 2;\n"
      "    cp1: coverpoint a iff (enable);\n"
      "    cp2: coverpoint b;\n"
      "    cp3: coverpoint c {\n"
      "      bins low = {[0:3]};\n"
      "      bins high = {[4:7]};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverGroup_ExtendsWithBody) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup child extends parent;\n"
      "    coverpoint z;\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverGroup_SampleFunctionWithBody) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg with function sample(int val);\n"
      "    coverpoint val {\n"
      "      bins low = {[0:127]};\n"
      "      bins high = {[128:255]};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverGroup_PortsWithBody) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg(ref int x, input int threshold);\n"
      "    coverpoint x {\n"
      "      bins below = {[0:threshold]};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverGroup_EmptyCrossBody) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2 {}\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverGroup_MultipleOptions) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    option.auto_bin_max = 64;\n"
      "    option.weight = 2;\n"
      "    option.goal = 95;\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverGroup_InPackage) {
  EXPECT_TRUE(ParseOk(
      "package p;\n"
      "  covergroup cg;\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endpackage\n"));
}

TEST(ParserA211, CoverGroup_NegedgeEvent) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg @(negedge rst_n);\n"
      "    coverpoint state;\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverGroup_ValueRangesInBins) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins a = {[$:50]};\n"
      "      bins b = {[51:100]};\n"
      "      bins c = {[101:$]};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverGroup_CrossThreeItems) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    a_cp: coverpoint a;\n"
      "    b_cp: coverpoint b;\n"
      "    c_cp: coverpoint c;\n"
      "    cross a_cp, b_cp, c_cp;\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverGroup_BinsWithCoverPointRef) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins b = {[0:15]} with (item < 10);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverGroup_WildcardIllegalIgnore) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      wildcard bins even = {4'b???0};\n"
      "      wildcard bins odd = {4'b???1};\n"
      "      illegal_bins overflow = {[200:255]};\n"
      "      ignore_bins reset = {0};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n"));
}

TEST(ParserA211, CoverGroup_ASTVerification) {
  auto r = Parse(
      "module m;\n"
      "  covergroup my_cg @(posedge clk);\n"
      "    coverpoint addr;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCovergroupDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "my_cg");
  EXPECT_EQ(item->kind, ModuleItemKind::kCovergroupDecl);
  EXPECT_TRUE(item->loc.IsValid());
}

TEST(ParserA211, CoverGroup_ExtendsASTVerification) {
  auto r = Parse(
      "module m;\n"
      "  covergroup child_cg extends parent_cg;\n"
      "    coverpoint z;\n"
      "  endgroup : child_cg\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCovergroupDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "child_cg");
}

TEST(ParserA211, CoverGroup_SampleFunctionASTVerification) {
  auto r = Parse(
      "module m;\n"
      "  covergroup sampled_cg with function sample(int data);\n"
      "    coverpoint data;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCovergroupDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "sampled_cg");
}

}  // namespace
