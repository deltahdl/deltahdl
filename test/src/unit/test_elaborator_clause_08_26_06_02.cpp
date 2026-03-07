// Non-LRM tests

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §8.26.6.2: Interface class inherits from two — no conflict if no
// overlapping names.
TEST(ElabA82662, NoConflictNoOverlapOk) {
  EXPECT_TRUE(ElabOk(
      "interface class A;\n"
      "  pure virtual function void fa();\n"
      "endclass\n"
      "interface class B;\n"
      "  pure virtual function void fb();\n"
      "endclass\n"
      "interface class C extends A, B;\n"
      "  pure virtual function void fc();\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n"));
}

}  // namespace
