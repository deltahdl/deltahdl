// §22.3: `resetall

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection22, ResetallDirective) {
  EXPECT_TRUE(
      ParseOk("`resetall\n"
              "module t;\n"
              "endmodule\n"));
}

}  // namespace
