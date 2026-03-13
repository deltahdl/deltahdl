#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §15.3.1: new() with explicit keyCount elaborates with init_expr.
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

// §15.3.1: new() with no arguments (default keyCount = 0).
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

// §15.3.1: new() with zero keyCount.
TEST(SemaphoreNewElaborator, NewWithZeroKeyCount) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  semaphore sem = new(0);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §15.3.1: Multiple semaphores each with new().
TEST(SemaphoreNewElaborator, MultipleNewInitializers) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  semaphore s1 = new(1);\n"
      "  semaphore s2 = new(5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 2u);
  EXPECT_NE(mod->variables[0].init_expr, nullptr);
  EXPECT_NE(mod->variables[1].init_expr, nullptr);
}

}  // namespace
