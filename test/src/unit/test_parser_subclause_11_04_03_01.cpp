
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DataTypeParsing, RealInExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  real a, b, c;\n"
              "  initial begin\n"
              "    a = 1.5;\n"
              "    b = 2.5;\n"
              "    c = a + b;\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
