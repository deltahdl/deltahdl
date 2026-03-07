// Non-LRM tests

#include <gtest/gtest.h>
#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §6.3.2.2: Drive strength on net declaration without assignment is error.
TEST(Elaborator, DriveStrengthOnNetDeclWithoutAssignIsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire (strong0, pull1) w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §6.3.2.2: Drive strength on net declaration with assignment is valid.
TEST(Elaborator, DriveStrengthOnNetDeclWithAssignIsValid) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire (strong0, pull1) w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
