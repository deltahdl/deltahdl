#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §13.3.1: items of an automatic task cannot be reached through a hierarchical
// reference. A hierarchical path into an automatic task's local is rejected.
TEST(StaticAutomaticTask, AutoTaskItemHierRefInContAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "  endtask\n"
      "  assign y = t.x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// Contrast: the same hierarchical path into a static task is permitted, so the
// §13.3.1 restriction must not fire for a static task.
TEST(StaticAutomaticTask, StaticTaskItemHierRefAllowed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  task static t();\n"
      "    int x;\n"
      "  endtask\n"
      "  assign y = t.x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The restriction also applies to references inside procedural blocks.
TEST(StaticAutomaticTask, AutoTaskItemHierRefInInitialError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  task automatic t();\n"
      "    int x;\n"
      "  endtask\n"
      "  initial y = t.x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
