#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(FunctionBackgroundProcessElaboration, ForkJoinNoneOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void my_func();\n"
      "    fork\n"
      "      a = 1;\n"
      "    join_none\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration, NonblockingAssignOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  function void set_x();\n"
      "    x <= 1;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration, EventTriggerOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  event e;\n"
      "  function void fire_event();\n"
      "    -> e;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §13.4.4: a clocking drive is one of the non-blocking statements that shall
// be allowed inside a function (alongside nonblocking assignments, event
// triggers, and fork-join_none). The synchronous drive syntax comes from the
// §14.16 dependency: a nonblocking assignment to a clocking-block output.
TEST(FunctionBackgroundProcessElaboration, ClockingDriveOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic sig;\n"
      "  clocking cb @(posedge clk);\n"
      "    output sig;\n"
      "  endclocking\n"
      "  function void drive_it();\n"
      "    cb.sig <= 1'b1;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration, DelayInsideForkJoinNoneOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void spawn_delayed();\n"
      "    fork\n"
      "      #10 $display(\"done\");\n"
      "    join_none\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration, ForkJoinError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void my_func();\n"
      "    fork\n"
      "      a = 1;\n"
      "    join\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration, ForkJoinAnyError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void my_func();\n"
      "    fork\n"
      "      a = 1;\n"
      "    join_any\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration, TaskEnableInsideForkJoinNoneOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task t(); endtask\n"
      "  function void f();\n"
      "    fork\n"
      "      t();\n"
      "    join_none\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration, ContAssignToFuncWithNbaError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic q;\n"
      "  logic r;\n"
      "  function automatic logic spawn_nba();\n"
      "    q <= 1'b1;\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  assign r = spawn_nba();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration,
     ContAssignToFuncWithForkJoinNoneError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic r;\n"
      "  function automatic logic spawn_bg();\n"
      "    fork\n"
      "      $display(\"bg\");\n"
      "    join_none\n"
      "    return 1'b1;\n"
      "  endfunction\n"
      "  assign r = spawn_bg();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration,
     ContAssignToFuncWithEventTriggerError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event e;\n"
      "  logic r;\n"
      "  function automatic logic spawn_trigger();\n"
      "    -> e;\n"
      "    return 1'b1;\n"
      "  endfunction\n"
      "  assign r = spawn_trigger();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration, NbEventTriggerOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  event e;\n"
      "  function void fire_nb();\n"
      "    ->> e;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration,
     ContAssignToFuncWithNbEventTriggerError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event e;\n"
      "  logic r;\n"
      "  function automatic logic spawn_nb_trigger();\n"
      "    ->> e;\n"
      "    return 1'b1;\n"
      "  endfunction\n"
      "  assign r = spawn_nb_trigger();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration, ContAssignToPureFuncOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic r;\n"
      "  function automatic logic pure_func(input logic a);\n"
      "    return ~a;\n"
      "  endfunction\n"
      "  logic in;\n"
      "  assign r = pure_func(in);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §13.4.4: the LRM's own illegal example is a variable-declaration
// initializer (`bit y = watch_for_zero(stack);`). A module-scope variable
// initializer runs at time zero, outside any initial/always/fork procedure,
// so calling a function that schedules a background event there is illegal.
TEST(FunctionBackgroundProcessElaboration, VarInitToBackgroundFuncNbaError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic q;\n"
      "  function automatic logic spawn_nba();\n"
      "    q <= 1'b1;\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  logic y = spawn_nba();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §13.4.4: a net-declaration assignment is a continuous assignment, another
// context in which the side effect of spawning a background event is not
// allowed.
TEST(FunctionBackgroundProcessElaboration, NetDeclInitToBackgroundFuncError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic q;\n"
      "  function automatic logic spawn_nba();\n"
      "    q <= 1'b1;\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  wire y = spawn_nba();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §13.4.4: a variable initializer that calls an ordinary function with no
// background side effect stays legal — the rule flags only the side effect.
TEST(FunctionBackgroundProcessElaboration, VarInitToPureFuncOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic logic pure_func(input logic a);\n"
      "    return ~a;\n"
      "  endfunction\n"
      "  logic in;\n"
      "  logic y = pure_func(in);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration, InitialCallToBackgroundFuncOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic q;\n"
      "  function automatic logic spawn_nba();\n"
      "    q <= 1'b1;\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  logic r;\n"
      "  initial r = spawn_nba();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
