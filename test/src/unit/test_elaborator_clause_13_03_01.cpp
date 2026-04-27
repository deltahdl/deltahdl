#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Lifetime-keyword acceptance on task declarations is a §6.21 rule;
// the corresponding elaborator tests (TaskDeclLifetimeAutomatic and
// TaskDeclLifetimeStatic) live in test_elaborator_clause_06_21.cpp.

TEST(TaskDeclElaboration, StaticVarInAutoTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task automatic work();\n"
      "    static int count = 0;\n"
      "    count = count + 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskDeclElaboration, AutoVarInStaticTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task static work();\n"
      "    automatic int temp = 0;\n"
      "    temp = temp + 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskDeclElaboration, DefaultLifetimeTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task my_task(input int n);\n"
      "    $display(\"%0d\", n);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskDeclElaboration, AutomaticVarInAutoTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task automatic work();\n"
      "    automatic int temp = 0;\n"
      "    temp = temp + 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskDeclElaboration, StaticVarInStaticTaskElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task static work();\n"
      "    static int count = 0;\n"
      "    count = count + 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
