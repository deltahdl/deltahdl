#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(Elaboration, EventVarIsEvent) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  event ev;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& v : mod->variables) {
    if (v.name == "ev") {
      found = true;
      EXPECT_TRUE(v.is_event);
    }
  }
  EXPECT_TRUE(found) << "event variable 'ev' not found";
}

TEST(Elaboration, EventDefaultInit_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  event ev;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, EventVarWidthZero) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  event ev;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  for (const auto& v : mod->variables) {
    if (v.name == "ev") {
      EXPECT_EQ(v.width, 0u);
    }
  }
}

}  // namespace
