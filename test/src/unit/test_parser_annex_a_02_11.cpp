#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(CovergroupDeclParsing, CoverageOption_AutoBinMax) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    option.auto_bin_max = 64;\n"
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

TEST(CovergroupDeclParsing, HierarchicalBtfIdentifier_Dotted) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg @@(begin top.dut.task1);\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

}  // namespace
