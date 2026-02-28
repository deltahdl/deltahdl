// §19.7: Specifying coverage options

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// §A.2.11 Production #2: coverage_spec_or_option
// =============================================================================
TEST(ParserA211, CoverageSpecOrOption_Option) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    option.auto_bin_max = 128;\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #3: coverage_option
// =============================================================================
TEST(ParserA211, CoverageOption_OptionMember) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    option.weight = 2;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverageOption_Goal) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    option.goal = 90;\n"
              "  endgroup\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.11 Production #22: bins_selection_or_option
// =============================================================================
TEST(ParserA211, BinsSelectionOrOption_CoverageOption) {
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

}  // namespace
