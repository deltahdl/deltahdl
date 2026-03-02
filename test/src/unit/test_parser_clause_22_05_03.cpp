// §22.5.3: `undefineall

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection22, UndefineallDirective) {
  EXPECT_TRUE(
      ParseOk("`define A 1\n"
              "`define B 2\n"
              "`undefineall\n"
              "module t;\n"
              "endmodule\n"));
}

}  // namespace
