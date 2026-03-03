// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserSection11, Sec11_1_ExprAsFunctionArgument) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  initial $display(a + b, c * d, {e, f});\n"
              "endmodule\n"));
}

}  // namespace
