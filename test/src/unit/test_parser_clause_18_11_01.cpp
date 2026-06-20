#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(SubroutineCallExprParsing, RandomizeCallWithNull) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize(null); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// 18.11.1: the special null argument is also accepted on a bare randomize()
// call, not only on an explicit obj.randomize(...). This exercises the other
// arm of the argument-list check that recognizes the callee as randomize. null
// names no property, yet it must not be flagged as an illegal expression
// argument.
TEST(SubroutineCallExprParsing, BareRandomizeCallWithNull) {
  auto r = Parse(
      "module m;\n"
      "  initial begin randomize(null); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
