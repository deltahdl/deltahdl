#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection22, DefineSimpleMacro) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define WIDTH 8\n"
              "module t;\n"
              "  logic [`WIDTH-1:0] data;\n"
              "endmodule\n"));
}

}
