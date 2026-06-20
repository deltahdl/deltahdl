#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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

}  // namespace
