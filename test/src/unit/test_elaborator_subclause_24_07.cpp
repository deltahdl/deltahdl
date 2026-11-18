#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ProgramControlTasksElab, ExitInProgramInitialElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program p;\n"
      "  initial $exit();\n"
      "endprogram\n",
      f, "p");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->processes.empty());
  EXPECT_EQ(mod->processes[0].kind, RtlirProcessKind::kInitial);
}

TEST(ProgramControlTasksElab, ExitInNestedProgramElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  program p;\n"
      "    initial begin\n"
      "      $exit();\n"
      "    end\n"
      "  endprogram\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramControlTasksElab, ExitInModuleInitialElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial $exit();\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramControlTasksElab, ExitInsideForkInProgramElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program p;\n"
      "  initial begin\n"
      "    fork\n"
      "      $exit();\n"
      "    join_none\n"
      "  end\n"
      "endprogram\n",
      f, "p");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProgramControlTasksElab,
     DISABLED_AnExitWithOneArgumentInAProgramIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "program p;\n"
      "  initial begin\n"
      "    $exit(1);\n"
      "  end\n"
      "endprogram\n",
      f, "p");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "'$exit' takes no arguments",
                            3, "24.7"));
}

TEST(ProgramControlTasksElab,
     DISABLED_AnExitWithTwoArgumentsInAProgramIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "program p;\n"
      "  initial $exit(1, 2);\n"
      "endprogram\n",
      f, "p");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "'$exit' takes no arguments",
                            2, "24.7"));
}

TEST(ProgramControlTasksElab,
     DISABLED_AnExitWithOneArgumentInAModuleIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial $exit(1);\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "'$exit' takes no arguments",
                            2, "24.7"));
}

TEST(ProgramControlTasksElab,
     DISABLED_AnExitWithTwoArgumentsInAModuleIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task k;\n"
      "    $exit(1, 2);\n"
      "  endtask\n"
      "  initial k();\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "'$exit' takes no arguments",
                            3, "24.7"));
}

TEST(ProgramControlTasksElab,
     AnExitWithEmptyParenthesesInAModuleIsNotReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    $exit();\n"
      "    $exit;\n"
      "  end\n"
      "endmodule\n",
      f, "m");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
