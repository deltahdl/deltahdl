// §8.23: Class scope resolution operator ::

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- class_scope ---
// class_type ::
TEST(ParserA221, ClassScope) {
  auto r = Parse(
      "class base_cls;\n"
      "  typedef int inner_t;\n"
      "endclass\n"
      "module m; base_cls::inner_t x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
