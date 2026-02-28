// §19.5.4: Wildcard specification of coverage point bins

#include "fixture_parser.h"

using namespace delta;

return nullptr;
}

namespace {

TEST(ParserA211, BinsOrOptions_WildcardBins) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      wildcard bins even = {4'b???0};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

}  // namespace
