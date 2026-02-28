// §19.7.1: Covergroup type options

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA211, CoverageOption_TypeOption) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    type_option.weight = 3;\n"
              "  endgroup\n"
              "endmodule\n"));
}

}  // namespace
