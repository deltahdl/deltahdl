#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(SubroutineOverviewElaboration, TaskEnablesTaskIsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task t1(); endtask\n"
      "  task t2(); t1(); endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineOverviewElaboration, TaskEnablesFunctionIsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f(); return 1; endfunction\n"
      "  task t();\n"
      "    int x;\n"
      "    x = f();\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineOverviewElaboration, TaskReturnsValueIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    return 42;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(SubroutineOverviewElaboration, TaskBareReturnIsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    return;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineOverviewElaboration, TaskNoReturnIsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    int x;\n"
      "    x = 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineOverviewElaboration, TaskWithDelayIsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    #10;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SubroutineOverviewElaboration, TaskWithEventControlIsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  task t();\n"
      "    @(posedge clk);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(Subroutines, FunctionAndTaskElaborate) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function int add(int a, int b);\n"
             "    return a + b;\n"
             "  endfunction\n"
             "  task do_nothing;\n"
             "  endtask\n"
             "endmodule\n"));
}

TEST(Subroutines, TaskAndFunctionCoexistElaborate) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  function int add(int a, int b); return a + b; endfunction\n"
             "  task do_nothing; endtask\n"
             "endmodule\n"));
}

}  // namespace
