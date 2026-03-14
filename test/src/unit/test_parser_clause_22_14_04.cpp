#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(CompilerDirectiveParsing, BeginKeywords1364_2001_noconfig) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1364-2001-noconfig\"\n"
                              "module t;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

}  // namespace
