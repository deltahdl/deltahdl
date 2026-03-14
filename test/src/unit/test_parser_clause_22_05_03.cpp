#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(CompilerDirectiveParsing, UndefineallDirective) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define A 1\n"
                              "`define B 2\n"
                              "`undefineall\n"
                              "module t;\n"
                              "endmodule\n"));
}

}  // namespace
