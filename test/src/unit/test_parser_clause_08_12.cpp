// §8.12: Assignment, renaming, and copying

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA24, ClassNewCopy) {
  // new expression (shallow copy)
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

}  // namespace
