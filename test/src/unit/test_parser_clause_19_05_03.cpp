// §19.5.3: Automatic bin creation for coverage points of integral expressions

#include "fixture_parser.h"

using namespace delta;


namespace {

// =============================================================================
// §A.2.11 Production #9: bins_or_empty
// =============================================================================
TEST(ParserA211, BinsOrEmpty_Semicolon) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "endmodule\n"));
}

}  // namespace
