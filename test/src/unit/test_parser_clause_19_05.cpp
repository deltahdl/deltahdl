// §19.5: Defining coverage points

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// §A.2.11 Production #4: coverage_spec
// =============================================================================
TEST(ParserA211, CoverageSpec_CoverPoint) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint addr;\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #8: cover_point
// =============================================================================
TEST(ParserA211, CoverPoint_BasicExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverPoint_Labeled) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    cp1: coverpoint addr;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverPoint_WithIff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint addr iff (enable);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverPoint_LabeledWithIff) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    my_cp: coverpoint data iff (valid);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverPoint_ComplexExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint (a + b);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, BinsOrEmpty_EmptyBraces) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {}\n"
              "  endgroup\n"
              "endmodule\n"));
}

}  // namespace
