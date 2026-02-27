// §8.8: Typed constructor calls

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- class_new ---
// [ class_scope ] new [ ( list_of_arguments ) ]
// | new expression
TEST(ParserA24, ClassNewNoArgs) {
  auto r = Parse(
      "class C;\n"
      "endclass\n"
      "module m;\n"
      "  C c = new;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
