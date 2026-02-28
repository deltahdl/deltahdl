// §19.8.1: Overriding the built-in sample method

#include "fixture_parser.h"

using namespace delta;


namespace {

TEST(ParserA211, CovergroupDecl_WithSampleFunction) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg with function sample(int x, bit y);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverageEvent_WithFunctionSample) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg with function sample(bit [3:0] val);\n"
              "    coverpoint val;\n"
              "  endgroup\n"
              "endmodule\n"));
}

}  // namespace
