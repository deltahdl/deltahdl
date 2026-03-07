// §28.11

#include <gtest/gtest.h>
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §6.3.2.2: Drive strength (highz0, highz1) is illegal.
TEST(Elaborator, DriveStrengthHighz0Highz1IsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire w;\n"
      "  assign (highz0, highz1) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
