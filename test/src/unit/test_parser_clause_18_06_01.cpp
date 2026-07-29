#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// 18.6.1: randomize() returns an int, but the call may also stand as a
// statement with the result discarded, the companion of the
// RandomizeCallReturnValueUsed case below. The A.8.2 randomize_call view of
// the same input is RandomizeCallBasic in test_parser_annex_a_08_02.cpp.
TEST(SubroutineCallExprParsing, RandomizeCallResultDiscarded) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize(); end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// 18.6.1: the built-in randomize() method is a function returning int, so a
// call may appear as a value-returning expression whose result is captured and
// tested. This mirrors the clause example: int success = p.randomize(); then
// branching on whether the result equals 1.
TEST(SubroutineCallExprParsing, RandomizeCallReturnValueUsed) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int success;\n"
      "    success = obj.randomize();\n"
      "    if (success == 1) success = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
