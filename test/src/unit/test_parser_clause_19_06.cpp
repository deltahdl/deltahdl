// §19.6: Defining cross coverage

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA211, CoverageSpec_CoverCross) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2;\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #17: cover_cross
// =============================================================================
TEST(ParserA211, CoverCross_Basic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverCross_Labeled) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    my_cross: cross cp1, cp2;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverCross_WithIff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint a;\n"
              "    cp2: coverpoint b;\n"
              "    cross cp1, cp2 iff (enable);\n"
              "  endgroup\n"
              "endmodule\n"));
}

}  // namespace
