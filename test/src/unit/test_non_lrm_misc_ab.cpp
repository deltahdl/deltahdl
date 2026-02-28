// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

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
