// §19.5.2: Specifying bins for transitions

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA211, BinsOrOptions_DefaultSequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins others = default sequence;\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

}  // namespace
