// §22.5.1: `define

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection22, DefineSimpleMacro) {
  EXPECT_TRUE(
      ParseOk("`define WIDTH 8\n"
              "module t;\n"
              "  logic [`WIDTH-1:0] data;\n"
              "endmodule\n"));
}

}  // namespace
