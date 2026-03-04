#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection22, DefineAndUndef) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define FOO 1\n"
                              "module t;\n"
                              "endmodule\n"
                              "`undef FOO\n"));
}

}  // namespace
