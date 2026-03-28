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

TEST(Elaborator, DriveStrengthOnTriWithAssignOk) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  tri (weak0, weak1) n = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Elaborator, DriveStrengthOnTriWithoutAssignIsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  tri (weak0, weak1) n;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(Elaborator, DriveStrengthPropagatedToImplicitContAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire (supply0, strong1) w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].drive_strength0, 5u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 4u);
}

}  // namespace
