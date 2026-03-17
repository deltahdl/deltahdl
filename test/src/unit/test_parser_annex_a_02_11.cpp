#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- covergroup_declaration ---

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

TEST(CovergroupDeclParsing, CovergroupDecl_WithBlockEvent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @@(begin test_phase or end test_phase);\n"
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
}

TEST(CovergroupDeclParsing, CoverGroup_ASTVerification) {
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

TEST(CovergroupDeclParsing, CoverGroup_InPackage) {
  EXPECT_TRUE(
      ParseOk("package p;\n"
              "  covergroup cg;\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endpackage\n"));
}

TEST(CovergroupDeclParsing, CovergroupDecl_FormalSyntax) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- coverage_event ---

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

TEST(CovergroupDeclParsing, CoverGroup_NegedgeEvent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @(negedge rst_n);\n"
              "    coverpoint state;\n"
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

TEST(CovergroupDeclParsing, CovergroupDecl_WithSampleFunction) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg with function sample(int x, bit y);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverGroup_SampleFunctionWithBody) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg with function sample(int val);\n"
              "    coverpoint val {\n"
              "      bins low = {[0:127]};\n"
              "      bins high = {[128:255]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverGroup_SampleFunctionASTVerification) {
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

// --- block_event_expression, hierarchical_btf_identifier ---

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

TEST(CovergroupDeclParsing, BlockEventExpression_BeginHierarchical) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @@(begin top.test.run_phase);\n"
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

TEST(CovergroupDeclParsing, HierarchicalBtfIdentifier_Simple) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @@(begin my_task);\n"
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

// --- coverage_spec_or_option, coverage_option ---

TEST(CovergroupDeclParsing, CoverageSpecOrOption_CoverSpec) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverageSpecOrOption_Option) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    option.auto_bin_max = 128;\n"
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

TEST(CovergroupDeclParsing, CoverageOption_OptionMember) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    option.weight = 2;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverageOption_Goal) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    option.goal = 90;\n"
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

// --- cover_point, bins_or_empty ---

TEST(CovergroupDeclParsing, CoverageSpec_CoverPoint) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint addr;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverPoint_BasicExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x;\n"
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

// --- bins_or_options, bins_keyword ---

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

TEST(CovergroupDeclParsing, BinsOrOptions_WithArraySize) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins b[4] = {[0:15]};\n"
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

TEST(CovergroupDeclParsing, BinsOrOptions_WithWithClause) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins b = {[0:15]} with (item > 5);\n"
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

TEST(CovergroupDeclParsing, CoverGroup_BinsWithCoverPointRef) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins b = {[0:15]} with (item < 10);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, BinsOrOptions_SetCovergroupExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins b = x;\n"
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

// --- covergroup_range_list, covergroup_value_range, covergroup_expression ---

TEST(CovergroupDeclParsing, CovergroupRangeList_Single) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {5};\n"
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

TEST(CovergroupDeclParsing, CovergroupExpression_Literal) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {10};\n"
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

// --- trans_list, trans_set, trans_range_list, repeat_range ---

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

TEST(CovergroupDeclParsing, TransSet_SingleRange) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1 => 3);\n"
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

TEST(CovergroupDeclParsing, TransRangeList_SimpleItem) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (0 => 1);\n"
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

TEST(CovergroupDeclParsing, TransItem_SingleValue) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (5 => 10);\n"
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

TEST(CovergroupDeclParsing, RepeatRange_SingleExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins t = (1 [* 5]);\n"
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

// --- cover_cross, cross_body ---

TEST(CovergroupDeclParsing, CoverageSpec_CoverCross) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2;\n"
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

TEST(CovergroupDeclParsing, ListOfCrossItems_Two) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2;\n"
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

TEST(CovergroupDeclParsing, CrossItem_CoverPointIdentifier) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp_a: coverpoint a;\n"
              "    cp_b: coverpoint b;\n"
              "    cross cp_a, cp_b;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CrossBody_Empty) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2;\n"
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

TEST(CovergroupDeclParsing, CoverGroup_CrossThreeItems) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    a_cp: coverpoint a;\n"
              "    b_cp: coverpoint b;\n"
              "    c_cp: coverpoint c;\n"
              "    cross a_cp, b_cp, c_cp;\n"
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

TEST(CovergroupDeclParsing, CrossBody_WithItems) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1);\n"
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

TEST(CovergroupDeclParsing, CrossSetExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1) intersect {[0:7]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// --- bins_selection, select_expression, select_condition, bins_expression ---

TEST(CovergroupDeclParsing, CrossBodyItem_BinsSelection) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins ab = binsof(cp1) intersect {[0:3]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, BinsSelectionOrOption_BinsSelection) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins selected = binsof(cp1);\n"
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

TEST(CovergroupDeclParsing, SelectExpression_SelectCondition) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1);\n"
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

TEST(CovergroupDeclParsing, SelectExpression_Parenthesized) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = (binsof(cp1) && binsof(cp2));\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, SelectCondition_Binsof) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, SelectCondition_BinsofIntersect) {
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

TEST(CovergroupDeclParsing, BinsExpression_Variable) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, BinsExpression_CoverPointDotBin) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1.low);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverGroup_CrossWithBinsSelection) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
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

// --- Comprehensive integration ---

TEST(CovergroupDeclParsing, FullCovergroup_MultipleElements) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
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

TEST(CovergroupDeclParsing, CoverGroup_MultipleCoverpoints) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
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

TEST(CovergroupDeclParsing, CoverGroup_PortsWithBody) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg(ref int x, input int threshold);\n"
              "    coverpoint x {\n"
              "      bins below = {[0:threshold]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// --- covergroup_declaration errors ---

TEST(CovergroupDeclParsing, ErrorMissingEndgroup) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x;\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, ErrorMissingCovergroupName) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  covergroup;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, ErrorMismatchedEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg1;\n"
      "  endgroup : cg2\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(CovergroupDeclParsing, ErrorMissingSemicolonAfterDecl) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  covergroup cg\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, ErrorUnclosedPortList) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  covergroup cg(ref int x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

// --- cover_point errors ---

TEST(CovergroupDeclParsing, ErrorCoverPointMissingSemicolon) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, ErrorCoverPointUnclosedBinsBlock) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {0};\n"
              "  endgroup\n"
              "endmodule\n"));
}

// --- cover_cross errors ---

TEST(CovergroupDeclParsing, ErrorCrossUnclosedBody) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, ErrorCrossMissingSemicolon) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2\n"
              "  endgroup\n"
              "endmodule\n"));
}

// --- bins_or_options errors ---

TEST(CovergroupDeclParsing, ErrorBinsMissingSemicolon) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {0}\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, ErrorBinsMissingEquals) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a {0};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// --- select_expression errors ---

TEST(CovergroupDeclParsing, ErrorBinsofMissingCloseParen) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1;\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// --- Edge cases: minimal and empty constructs ---

TEST(CovergroupDeclParsing, MinimalCovergroupDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, EmptyCovergroupDeclInClass) {
  EXPECT_TRUE(
      ParseOk("class c;\n"
              "  covergroup cg;\n"
              "  endgroup\n"
              "endclass\n"));
}

// --- Multiple covergroup declarations ---

TEST(CovergroupDeclParsing, MultipleCovergroupDecls) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg1;\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "  covergroup cg2;\n"
      "    coverpoint y;\n"
      "  endgroup\n"
      "  covergroup cg3;\n"
      "    coverpoint z;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(
      CountItemsByKind(r.cu->modules[0]->items, ModuleItemKind::kCovergroupDecl),
      3u);
}

// --- Covergroup with all spec types combined ---

TEST(CovergroupDeclParsing, CovergroupWithAllSpecTypes) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @(posedge clk);\n"
              "    option.auto_bin_max = 64;\n"
              "    type_option.weight = 2;\n"
              "    cp1: coverpoint addr {\n"
              "      bins low = {[0:63]};\n"
              "      bins high = {[64:255]};\n"
              "      wildcard bins even = {8'b???????0};\n"
              "      illegal_bins overflow = {[256:$]};\n"
              "      ignore_bins zero = {0};\n"
              "      bins def = default;\n"
              "    }\n"
              "    cp2: coverpoint data iff (valid);\n"
              "    cross cp1, cp2 {\n"
              "      bins sel = binsof(cp1) intersect {[0:63]};\n"
              "      ignore_bins ig = binsof(cp1) intersect {0};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

// --- coverage_event validation ---

TEST(CovergroupDeclParsing, ErrorWithFunctionWrongName) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  covergroup cg with function foo(int x);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, ErrorBlockEventMissingBeginOrEnd) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  covergroup cg @@(foo);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, BlockEventExpressionValid) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @@(begin task1 or end task2);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, BlockEventHierarchicalPath) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @@(begin top.dut.phase or end top.dut.phase);\n"
              "  endgroup\n"
              "endmodule\n"));
}

}  // namespace
