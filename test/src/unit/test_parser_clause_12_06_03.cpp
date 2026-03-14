#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(PatternConditionalParsing, MatchesInTernary) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    y = (x matches 5) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternConditionalParsing, MatchesWithGuardInTernary) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    y = (x matches 5 &&& en) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(PatternConditionalParsing, MatchesWildcardInTernary) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    y = (sel matches 4'bx1x0) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
