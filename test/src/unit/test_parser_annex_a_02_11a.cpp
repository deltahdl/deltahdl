#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

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
  // The unterminated body swallows 'endmodule', so the covergroup is what runs
  // out of source, and the end of the source stands on line 5, the line the
  // trailing newline opened.
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
  // §9.3.4 owns the end-label rule Parser::MatchEndLabel enforces for every
  // named block, the covergroup included; §19.3 has no report of its own here.
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
  // 'coverpoint' stands where the ';' was demanded.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'coverpoint'", 3, "19.3"));
}

TEST(CovergroupDeclParsing, ErrorUnclosedPortList) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg(ref int x;\n"
      "  endgroup\n"
      "endmodule\n");
  // The unclosed formal list scans to the end of the source, so the ';' that
  // ends the covergroup declaration is demanded at EOF, on line 5.
  EXPECT_TRUE(ReportedError(r.diags, "expected ';', got EOF", 5, "19.3"));
}

TEST(CovergroupDeclParsing, ErrorCoverPointMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  covergroup cg;\n"
      "    coverpoint x\n"
      "  endgroup\n"
      "endmodule\n");
  // The unterminated coverpoint swallows 'endgroup' and 'endmodule', so the
  // covergroup runs out of source at line 6.
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
  // The unclosed coverpoint body swallows 'endgroup', so the covergroup runs
  // out of source at line 7.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endgroup', got EOF", 7, "19.3"));
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
  // The unclosed cross body swallows 'endgroup', so the covergroup runs out of
  // source at line 9.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'endgroup', got EOF", 9, "19.3"));
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
  // The unterminated cross swallows 'endgroup' and 'endmodule', so the
  // covergroup runs out of source at line 8.
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
  // The coverpoint body's closing '}' on line 5 is where the missing ';' is
  // detected.
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
  // §19.5.1 owns the bins_selection '=' the header scan demands; §19.3 has no
  // report of its own here.
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
  // The unbalanced paren is reported where the cross body closes, on line 7.
  EXPECT_TRUE(
      ReportedError(r.diags, "missing ')' in covergroup item", 7, "19.3"));
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

}  // namespace
