#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(SemaphoreNewElaborator, NewWithExplicitKeyCount) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  semaphore sem = new(3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].class_type_name, "semaphore");
  EXPECT_NE(mod->variables[0].init_expr, nullptr);
}

TEST(SemaphoreNewElaborator, NewWithDefaultKeyCount) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  semaphore sem = new();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].class_type_name, "semaphore");
  EXPECT_NE(mod->variables[0].init_expr, nullptr);
}

}  // namespace
