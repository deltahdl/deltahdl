// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// §A.2.11 Production #25: select_condition
// =============================================================================
TEST(ParserA211, SelectCondition_Binsof) {
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

TEST(ParserA211, SelectCondition_BinsofIntersect) {
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

// =============================================================================
// §A.2.11 Production #26: bins_expression
// =============================================================================
TEST(ParserA211, BinsExpression_Variable) {
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

TEST(ParserA211, BinsExpression_CoverPointDotBin) {
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

// =============================================================================
// §A.2.11 Production #27: covergroup_range_list
// =============================================================================
TEST(ParserA211, CovergroupRangeList_Single) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {5};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CovergroupRangeList_Multiple) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {1, 2, 3, 4, 5};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CovergroupRangeList_MixedRanges) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
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
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {42};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CovergroupValueRange_ClosedRange) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {[0:255]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CovergroupValueRange_OpenLow) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {[$:100]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CovergroupValueRange_OpenHigh) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
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
  EXPECT_TRUE(
      ParseOk("module m;\n"
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
  EXPECT_TRUE(
      ParseOk("module m;\n"
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
  EXPECT_TRUE(
      ParseOk("module m;\n"
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

// =============================================================================
// §A.2.11 Production #33: covergroup_expression
// =============================================================================
TEST(ParserA211, CovergroupExpression_Literal) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins a = {10};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CovergroupExpression_BinaryOp) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
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

TEST(ParserA211, CoverGroup_AllBinTypes) {
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

TEST(ParserA211, CoverGroup_TransitionBins) {
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

TEST(ParserA211, CoverGroup_CrossWithBinsSelection) {
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

TEST(ParserA211, CoverGroup_MultipleCoverpoints) {
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

TEST(ParserA211, CoverGroup_ExtendsWithBody) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup child extends parent;\n"
              "    coverpoint z;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_SampleFunctionWithBody) {
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

}  // namespace
