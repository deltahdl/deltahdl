// §8.25.1: Class scope resolution operator for parameterized classes

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- class_type ---
// ps_class_identifier [param] { :: class_identifier [param] }
TEST(ParserA221, ClassTypeParameterized) {
  auto r = Parse(
      "class param_cls #(type T = int);\n"
      "  typedef T value_t;\n"
      "endclass\n"
      "module m; param_cls#(int)::value_t x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
