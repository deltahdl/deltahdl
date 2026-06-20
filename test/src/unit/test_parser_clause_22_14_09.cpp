#include "fixture_parser.h"

using namespace delta;

namespace {

// The begin_keywords/version_specifier grammar belongs to §22.14 and is
// version-agnostic at the parser stage; one smoke test confirms a §22.14.9
// version_specifier flows through to a normal module parse.
TEST(CompilerDirectiveParsing, BeginKeywords1800_2017) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2017\"\n"
                              "module t;\n"
                              "  logic [7:0] data;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

}  // namespace
