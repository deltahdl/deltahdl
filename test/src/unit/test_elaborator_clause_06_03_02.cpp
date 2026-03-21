#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Elaborator, DriveStrengthOnNetDeclWithAssignOk) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire (strong0, pull1) w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elaborator, DriveStrengthOnNetDeclWithoutAssignIsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire (strong0, pull1) w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
