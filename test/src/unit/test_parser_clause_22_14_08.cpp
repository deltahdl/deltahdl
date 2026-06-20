#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(CompilerDirectiveParsing, BeginKeywords1800_2012) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2012\"\n"
                              "module t;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

}  // namespace
