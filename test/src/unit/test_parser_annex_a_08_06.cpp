// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA86, UnaryModulePathReductionAnd) {
  auto r = Parse(
      "module m(input [3:0] a, output y);\n"
      "  specify\n"
      "    if (&a) (a[0] => y) = 11;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
