#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

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

TEST(CovergroupDeclParsing, ErrorMissingEndgroup) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x;\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endgroup', got EOF", 5, "19.3"));
}

TEST(CovergroupDeclParsing, ErrorMissingCovergroupName) {
  auto r = Parse(
      "module m;\n"
      "  covergroup;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 2, "19.3"));
}

TEST(CovergroupDeclParsing, ErrorMismatchedEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg1;\n"
      "  endgroup : cg2\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "end label 'cg2' does not match 'cg1'", 3,
                            "9.3.4"));
}

TEST(CovergroupDeclParsing, ErrorMissingSemicolonAfterDecl) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'coverpoint'", 3, "19.3"));
}

TEST(CovergroupDeclParsing, ErrorUnclosedPortList) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg(ref int x;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got ';'", 2, "19.3"));
}

TEST(CovergroupDeclParsing, ErrorCoverPointMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endgroup', got EOF", 6, "19.3"));
}

TEST(CovergroupDeclParsing, ErrorCoverPointUnclosedBinsBlock) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins a = {0};\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '}', got 'endgroup'", 5, "A.2.11"));
}

TEST(CovergroupDeclParsing, ErrorCrossUnclosedBody) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2 {\n"
      "      bins sel = binsof(cp1);\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '}', got 'endgroup'", 7, "A.2.11"));
}

TEST(CovergroupDeclParsing, ErrorCrossMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endgroup', got EOF", 8, "19.3"));
}

TEST(CovergroupDeclParsing, ErrorBinsMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins a = {0}\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "missing ';' in covergroup item", 5, "19.3"));
}

TEST(CovergroupDeclParsing, ErrorBinsMissingEquals) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins a {0};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '=' in bins declaration", 4, "19.5.1"));
}

TEST(CovergroupDeclParsing, ErrorBinsofMissingCloseParen) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp1: coverpoint a;\n"
      "    cp2: coverpoint b;\n"
      "    cross cp1, cp2 {\n"
      "      bins sel = binsof(cp1;\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "missing ')' in covergroup item", 6, "19.3"));
}

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
  EXPECT_EQ(CountItemsByKind(r.cu->modules[0]->items,
                             ModuleItemKind::kCovergroupDecl),
            3u);
}

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

TEST(CovergroupDeclParsing, ErrorWithFunctionWrongName) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg with function foo(int x);\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'sample', got 'foo'", 2, "19.3"));
}

TEST(CovergroupDeclParsing, ErrorBlockEventMissingBeginOrEnd) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg @@(foo);\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected 'begin' or 'end' in block event",
                            2, "19.3"));
}

TEST(CovergroupDeclParsing, HierarchicalBtfIdentifier_ClassScope) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @@(begin C::m);\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, HierarchicalBtfIdentifier_ParameterizedClassScope) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @@(end pkg::C#(8)::m or begin D#(.W(4))::n);\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, HierarchicalBtfIdentifier_RootAndBitSelect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @@(begin $root.top.g[0].u[1][2].blk);\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing,
     HierarchicalBtfIdentifier_RootWithoutDotIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg @@(begin $root top.t);\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected '.'", 2, "A.2.11"));
}

TEST(CovergroupDeclParsing, CoverageOption_MemberWithoutValueIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    option.auto_bin_max;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a coverage option is set as 'option.member = value'", 3,
      "A.2.11"));
}

TEST(CovergroupDeclParsing, CoverageOption_KeywordWithoutMemberIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    type_option = 3;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a coverage option is set as 'type_option.member = value'", 3,
      "A.2.11"));
}

TEST(CovergroupDeclParsing, CoverageOption_InCoverpointBodyWithoutValue) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      option.weight;\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a coverage option is set as 'option.member = value'", 4,
      "A.2.11"));
}

TEST(CovergroupDeclParsing, CoverageOption_InCrossBodyWithoutMember) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    a: coverpoint x;\n"
      "    b: coverpoint y;\n"
      "    cross a, b {\n"
      "      type_option = 1;\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a coverage option is set as 'type_option.member = value'", 6,
      "A.2.11"));
}

TEST(CovergroupDeclParsing, AttributeInstance_PrecedesCoverageSpec) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    (* full *) coverpoint x {\n"
      "      bins b {1};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '=' in bins declaration", 4, "19.5.1"));
}

TEST(CovergroupDeclParsing, AttributeInstance_PrecedesCoverageOption) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    (* a = 1 *) option.weight = 1;\n"
      "    option.weight = 2;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "coverage option 'option.weight' is assigned more than once", 4,
      "19.7"));
}

TEST(CovergroupDeclParsing, CoverPoint_DataTypeBeforeLabelReadsBody) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    int cp: coverpoint x {\n"
      "      bins b {1};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '=' in bins declaration", 4, "19.5.1"));
}

TEST(CovergroupDeclParsing, CoverPoint_ImplicitDataTypeBeforeLabel) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    signed [7:0] cp1: coverpoint x;\n"
              "    [3:0] cp2: coverpoint y;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverPoint_WithoutExpressionIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    cp: coverpoint;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a coverpoint covers an expression; none is written", 3,
      "A.2.11"));
}

TEST(CovergroupDeclParsing, CoverPoint_BodyWithoutExpressionIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint { bins b = {1}; }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a coverpoint covers an expression; none is written", 3,
      "A.2.11"));
  EXPECT_FALSE(
      ReportedError(r.diags, "expected '=' in bins declaration", 3, "19.5.1"));
}

TEST(CovergroupDeclParsing, CoverPoint_ConcatenationExpressionThenBody) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint {a, b} {\n"
      "      bins b {1};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '=' in bins declaration", 4, "19.5.1"));
}

TEST(CovergroupDeclParsing, CoverPoint_BareIffGuardIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x iff en;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a coverage guard is written 'iff ( expression )'",
                            3, "A.2.11"));
}

TEST(CovergroupDeclParsing, CoverCross_BareIffGuardIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    a: coverpoint x;\n"
      "    b: coverpoint y;\n"
      "    cross a, b iff {\n"
      "      bins s = binsof(a);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a coverage guard is written 'iff ( expression )'",
                            5, "A.2.11"));
  EXPECT_EQ(r.diags.size(), 1u);
}

TEST(CovergroupDeclParsing, BinsSelection_WildcardInCrossIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    a: coverpoint x;\n"
      "    b: coverpoint y;\n"
      "    cross a, b {\n"
      "      wildcard bins s = binsof(a);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "a bins_selection admits no 'wildcard'", 6,
                            "A.2.11"));
}

TEST(CovergroupDeclParsing, BinsSelection_ArrayInCrossIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    a: coverpoint x;\n"
      "    b: coverpoint y;\n"
      "    cross a, b {\n"
      "      bins s[] = binsof(a);\n"
      "      bins t[2] = binsof(b);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "a cross bin is not an array", 6, "A.2.11"));
  EXPECT_TRUE(
      ReportedError(r.diags, "a cross bin is not an array", 7, "A.2.11"));
}

TEST(CovergroupDeclParsing, BinsSelection_DefaultInCrossIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    a: coverpoint x;\n"
      "    b: coverpoint y;\n"
      "    cross a, b {\n"
      "      bins s = default;\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "'default' is a coverpoint bin", 6, "A.2.11"));
}

TEST(CovergroupDeclParsing, BinsOrOptions_WildcardDefaultIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      wildcard bins d = default;\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "a 'default' bin takes none", 4, "A.2.11"));
}

TEST(CovergroupDeclParsing, BinsOrOptions_DefaultSequenceArrayIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins d[] = default sequence;\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "a 'default sequence' bin is not an array",
                            4, "A.2.11"));
}

TEST(CovergroupDeclParsing, BinsOrOptions_SizedTransitionArrayIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x {\n"
      "      bins t[4] = (1 => 2), (2 => 3);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a transition bin's array is written '[ ]'", 4, "A.2.11"));
}

TEST(CovergroupDeclParsing, BinsOrOptions_WildcardTransitionAndSizedValue) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      wildcard bins t[] = (4'b1x0x => 4'b0xx1);\n"
              "      bins v[4] = {[0:15]};\n"
              "      bins d[2] = default;\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(CovergroupDeclParsing, CoverageOption_DotWithoutMemberIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    option. = 3;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a coverage option is set as 'option.member = value'", 3,
      "A.2.11"));
}

TEST(CovergroupDeclParsing, CovergroupItem_OtherThanSpecOrOptionIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  int a;\n"
      "  covergroup cg;\n"
      "    lbl : a;\n"
      "    int x;\n"
      "    ;\n"
      "    coverpoint a;\n"
      "  endgroup\n"
      "endmodule\n");
  for (int line : {4, 5, 6}) {
    EXPECT_TRUE(ReportedError(
        r.diags,
        "a covergroup item is a coverpoint, a cross or a coverage "
        "option",
        line, "A.2.11"));
  }
  EXPECT_EQ(r.diags.size(), 3u);
}

TEST(CovergroupDeclParsing, SemicolonAfterACoverpointOrCrossBodyIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  int a, b;\n"
      "  covergroup cg;\n"
      "    cp_a : coverpoint a { bins one = {1}; };\n"
      "    cp_b : coverpoint b { bins two = {2}; }\n"
      "    x : cross cp_a, cp_b { bins s = binsof(cp_a); };\n"
      "  endgroup\n"
      "endmodule\n");
  for (int line : {4, 6}) {
    EXPECT_TRUE(ReportedError(
        r.diags,
        "a covergroup item is a coverpoint, a cross or a coverage "
        "option",
        line, "A.2.11"));
  }
  EXPECT_EQ(r.diags.size(), 2u);
}

TEST(CovergroupDeclParsing, BinsOrOptions_OtherThanBinsOrOptionIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  int a;\n"
      "  covergroup cg;\n"
      "    coverpoint a {\n"
      "      bins b = {1};;\n"
      "      wildcard a;\n"
      "      a;\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  for (int line : {5, 6, 7}) {
    EXPECT_TRUE(ReportedError(
        r.diags,
        "a coverpoint body item is a bins declaration or a coverage "
        "option",
        line, "A.2.11"));
  }
  EXPECT_EQ(r.diags.size(), 3u);
}

TEST(CovergroupDeclParsing,
     CrossBodyItem_OtherThanSelectionOrOptionIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  int a, b;\n"
      "  covergroup cg;\n"
      "    cross a, b {\n"
      "      bins s = binsof(a);;\n"
      "      a;\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  for (int line : {5, 6}) {
    EXPECT_TRUE(ReportedError(
        r.diags,
        "a cross body item is a bins selection, a coverage option or "
        "a function declaration",
        line, "A.2.11"));
  }
  EXPECT_EQ(r.diags.size(), 2u);
}

TEST(CovergroupDeclParsing, BinsOrOptions_BrokenItemBeforeCloseBrace) {
  auto r = Parse(
      "module m;\n"
      "  int a;\n"
      "  covergroup cg;\n"
      "    coverpoint a { bins b }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '=' in bins declaration", 4, "19.5.1"));
  EXPECT_EQ(r.diags.size(), 1u);
}

TEST(CovergroupDeclParsing, BinsSelection_MissingEqualsIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  int a, b;\n"
      "  covergroup cg;\n"
      "    cross a, b {\n"
      "      bins s binsof(a);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '=' in bins declaration", 5, "19.5.1"));
  EXPECT_EQ(r.diags.size(), 1u);
}

TEST(CovergroupDeclParsing, BodyItem_MissingSemicolonBeforeEachItemKind) {
  auto r = Parse(
      "module m;\n"
      "  int a, b;\n"
      "  covergroup cg;\n"
      "    coverpoint a {\n"
      "      bins b1 = {1}\n"
      "      bins b2 = {2}\n"
      "      wildcard bins b3 = {3}\n"
      "      (* note *) bins b4 = {4}\n"
      "      option.weight = 2\n"
      "      bins b5 = {5} a b;\n"
      "    }\n"
      "    cross a, b {\n"
      "      bins s = binsof(a)\n"
      "      function int f();\n"
      "        return 0;\n"
      "      endfunction\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n");
  for (int line : {6, 7, 8, 9, 10, 14}) {
    EXPECT_TRUE(
        ReportedError(r.diags, "missing ';' in covergroup item", line, "19.3"));
  }
  EXPECT_EQ(r.diags.size(), 7u);
}

}  // namespace
