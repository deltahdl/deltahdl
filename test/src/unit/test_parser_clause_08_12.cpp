#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA24, ClassNewCopy) {
  auto r = Parse(
      "class C;\n"
      "endclass\n"
      "module m;\n"
      "  C c1, c2;\n"
      "  initial c2 = new c1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection8, ShallowCopy) {
  auto r = Parse(
      "module m;\n"
      "  class Packet;\n"
      "    int data;\n"
      "  endclass\n"
      "  initial begin\n"
      "    Packet p1, p2;\n"
      "    p1 = new;\n"
      "    p2 = new p1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

}  // namespace
