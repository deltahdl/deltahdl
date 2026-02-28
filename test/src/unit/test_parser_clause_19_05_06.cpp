// §19.5.6: Specifying Illegal coverage point values or transitions

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA211, BinsKeyword_IllegalBins) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      illegal_bins bad = {255};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

}  // namespace
