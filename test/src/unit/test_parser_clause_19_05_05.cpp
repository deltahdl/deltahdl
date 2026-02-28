// §19.5.5: Excluding coverage point values or transitions

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA211, BinsKeyword_IgnoreBins) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      ignore_bins skip = {128};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

}  // namespace
