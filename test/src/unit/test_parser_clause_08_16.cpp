// §8.16: Casting

#include "fixture_parser.h"

using namespace delta;

namespace {

// Use of type(this) as return type for singleton pattern.
// =============================================================================
// Section 8.16 -- Casting
// =============================================================================
// $cast system call with class handles.
TEST(ParserSection8, DynamicCastClassHandles) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  class Base;\n"
              "    int x;\n"
              "  endclass\n"
              "  class Derived extends Base;\n"
              "    int y;\n"
              "  endclass\n"
              "  initial begin\n"
              "    Base b;\n"
              "    Derived d;\n"
              "    d = new;\n"
              "    b = d;\n"
              "    $cast(d, b);\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
