#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA60703, MatchesInTernary) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    y = (x matches 5) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA60703, MatchesWithGuardInTernary) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    y = (x matches 5 &&& en) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA60703, MatchesWildcardInTernary) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    y = (sel matches 4'bx1x0) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}
