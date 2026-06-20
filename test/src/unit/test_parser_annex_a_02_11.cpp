#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(CovergroupDeclParsing, CovergroupDecl_Basic) {
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

TEST(CovergroupDeclParsing, CovergroupDecl_WithClockingEvent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @(posedge clk);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CovergroupDecl_WithPortList) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg(ref int x, input bit [3:0] y);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CovergroupDecl_WithPortsAndEvent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg(ref int x) @(posedge clk);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CovergroupDecl_WithEndLabel) {
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

TEST(CovergroupDeclParsing, CovergroupDecl_WithEmptyPortList) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg();\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CovergroupDecl_InClass) {
  EXPECT_TRUE(
      ParseOk("class c;\n"
              "  covergroup cg;\n"
              "  endgroup\n"
              "endclass\n"));
}

TEST(CovergroupDeclParsing, CovergroupDecl_WithExtends) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup child extends parent;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverGroup_ExtendsWithBody) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup child extends parent;\n"
              "    coverpoint z;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverGroup_ExtendsASTVerification) {
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
  EXPECT_EQ(item->covergroup_extends_base, "parent_cg");
}

// covergroup_declaration's second alternative: `covergroup extends base ;`
// names no new covergroup of its own. The parser takes the identifier that
// follows `extends` as both the declared name and the inherited base, so a
// derived covergroup written this way resolves under the base's name. This
// branch is distinct from the `covergroup child extends parent ;` form, which
// supplies a fresh name before `extends`.
TEST(CovergroupDeclParsing, CovergroupExtendsWithoutOwnName) {
  auto r = Parse(
      "module m;\n"
      "  covergroup extends base_cg;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCovergroupDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "base_cg");
  EXPECT_EQ(item->covergroup_extends_base, "base_cg");
}

TEST(CovergroupDeclParsing, CoverGroup_InPackage) {
  EXPECT_TRUE(
      ParseOk("package p;\n"
              "  covergroup cg;\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endpackage\n"));
}

TEST(CovergroupDeclParsing, CoverageEvent_ClockingEvent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @(posedge clk);\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverageEvent_NegedgeClocking) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @(negedge clk);\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverageEvent_WithFunctionSample) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg with function sample(bit [3:0] val);\n"
              "    coverpoint val;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverageEvent_BlockEventBegin) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @@(begin test_phase);\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverageEvent_BlockEventEnd) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @@(end test_phase);\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, BlockEventExpression_Or) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @@(begin phase1 or end phase2);\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, BlockEventExpression_MultipleOr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @@(begin a or begin b or end c);\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, HierarchicalBtfIdentifier_Dotted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @@(begin top.dut.task1);\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverageSpecOrOption_CoverSpec) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverageOption_AutoBinMax) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    option.auto_bin_max = 64;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverageOption_TypeOption) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    type_option.weight = 3;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverGroup_MultipleOptions) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    option.auto_bin_max = 64;\n"
              "    option.weight = 2;\n"
              "    option.goal = 95;\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, BinsSelectionOrOption_CoverageOption) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      option.weight = 5;\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverageSpec_CoverPoint) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint addr;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverPoint_Labeled) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint addr;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverPoint_WithIff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint addr iff (enable);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverPoint_LabeledWithIff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    my_cp: coverpoint data iff (valid);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverPoint_ComplexExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint (a + b);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverPoint_WithDataType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint x {\n"
              "      bins low = {[0:3]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, BinsOrEmpty_EmptyBraces) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {}\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, BinsOrEmpty_Semicolon) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverPoint_WithBinsBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {0, 1};\n"
              "      bins b = {2, 3};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, BinsOrEmpty_WithBraces) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {1};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, BinsKeyword_Bins) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {0};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, BinsKeyword_IgnoreBins) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      ignore_bins skip = {128};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, BinsKeyword_IllegalBins) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      illegal_bins bad = {255};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, BinsOrOptions_AutoSizedArray) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins b[] = {[0:15]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, BinsOrOptions_WithIff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins b = {[0:3]} iff (enable);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, BinsOrOptions_Default) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins others = default;\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, BinsOrOptions_DefaultSequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins others = default sequence;\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, BinsOrOptions_WildcardBins) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      wildcard bins even = {4'b???0};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, BinsOrOptions_ValueRangeList) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins low = {[0:3]};\n"
              "      bins mid = {[4:7]};\n"
              "      bins high = {[8:15]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, WithCovergroupExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins b = {[0:255]} with (item > 10);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, SetCovergroupExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins b = x;\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverGroup_AllBinTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
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

TEST(CovergroupDeclParsing, CoverGroup_WildcardIllegalIgnore) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
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

TEST(CovergroupDeclParsing, CovergroupRangeList_Multiple) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {1, 2, 3, 4, 5};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CovergroupRangeList_MixedRanges) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {1, [3:5], 8, [10:15]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CovergroupValueRange_SingleValue) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {42};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CovergroupValueRange_ClosedRange) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {[0:255]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CovergroupValueRange_OpenLow) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {[$:100]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CovergroupValueRange_OpenHigh) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {[100:$]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CovergroupValueRange_PlusMinusTolerance) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {[10 +/- 3]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CovergroupValueRange_PercentTolerance) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {[100 +%- 10]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, IntegerCovergroupExpression_Expr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins b[4] = {[0:15]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CovergroupExpression_BinaryOp) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {a + b};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverGroup_ValueRangesInBins) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {[$:50]};\n"
              "      bins b = {[51:100]};\n"
              "      bins c = {[101:$]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, TransList_Single) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1 => 2);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, TransList_Multiple) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1 => 2), (3 => 4);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, TransSet_MultipleRanges) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1 => 3 => 5);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, TransRangeList_ConsecutiveRepeat) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1 [* 3]);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, TransRangeList_GotoRepeat) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1 [-> 3]);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, TransRangeList_NonConsecutiveRepeat) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1 [= 3]);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, TransItem_MultipleValues) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1, 2, 3 => 4, 5);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, RepeatRange_Range) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1 [* 2:5]);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverGroup_TransitionBins) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
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

TEST(CovergroupDeclParsing, CoverCross_Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverCross_Labeled) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    my_cross: cross cp1, cp2;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverCross_WithIff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 iff (enable);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, ListOfCrossItems_Three) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cp3: coverpoint c;\n"
              "    cross cp1, cp2, cp3;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverGroup_EmptyCrossBody) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {}\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverCross_WithBody) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1) intersect {[0:3]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CrossBodyItem_FunctionDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
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

TEST(CovergroupDeclParsing, BinsSelection_Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins my_bin = binsof(cp1);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, BinsSelection_WithIff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1) iff (enable);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, SelectExpression_Negated) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = !binsof(cp1);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, SelectExpression_And) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1) && binsof(cp2);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, SelectExpression_Or) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1) || binsof(cp2);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}


}  // namespace
