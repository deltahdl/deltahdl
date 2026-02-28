// §19.6.1: Defining cross coverage bins

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA211, CoverCross_WithBody) {
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

TEST(ParserA211, CrossBody_WithItems) {
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

// =============================================================================
// §A.2.11 Production #21: cross_body_item
// =============================================================================
TEST(ParserA211, CrossBodyItem_BinsSelection) {
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

TEST(ParserA211, BinsSelectionOrOption_BinsSelection) {
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

// =============================================================================
// §A.2.11 Production #23: bins_selection
// =============================================================================
TEST(ParserA211, BinsSelection_Basic) {
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

TEST(ParserA211, BinsSelection_WithIff) {
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

// =============================================================================
// §A.2.11 Production #24: select_expression
// =============================================================================
TEST(ParserA211, SelectExpression_SelectCondition) {
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

TEST(ParserA211, SelectExpression_Negated) {
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

TEST(ParserA211, SelectExpression_And) {
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

TEST(ParserA211, SelectExpression_Or) {
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

TEST(ParserA211, SelectExpression_Parenthesized) {
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

}  // namespace
