#include "fixture_parser.h"

using namespace delta;

namespace {

// §8.30.1: weak_reference declaration parses OK.
TEST(ParserSection8, WeakReferenceDecl) {
  EXPECT_TRUE(ParseOk(
      "class my_obj;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    weak_reference #(my_obj) wr;\n"
      "  end\n"
      "endmodule\n"));
}

// §8.30.1: weak_reference used as class member.
TEST(ParserSection8, WeakReferenceAsMember) {
  EXPECT_TRUE(ParseOk(
      "class my_obj;\n"
      "  int x;\n"
      "endclass\n"
      "class holder;\n"
      "  weak_reference #(my_obj) wr;\n"
      "endclass\n"));
}

}  // namespace
