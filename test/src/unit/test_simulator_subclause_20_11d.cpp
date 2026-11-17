#include <gtest/gtest.h>

#include <string>

#include "helpers_assert_control_runs.h"

using namespace delta;

namespace {

TEST(AssertStatusControlSim,
     OffAndKillStopAFinalDeferredAssertionAndOnRestoresIt) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  initial begin\n"
      "    $assertoff;\n"
      "    assert final (0) else $display(\"off\");\n"
      "    #1 $asserton;\n"
      "    assert final (0) else $display(\"on\");\n"
      "    #1 $assertkill;\n"
      "    assert final (0) else $display(\"killed\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "on\n");
}

TEST(AssertStatusControlSim, AssertOffLeavesAnExpectChecked) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  logic clk = 0;\n"
      "  initial repeat (4) #5 clk = ~clk;\n"
      "  initial begin\n"
      "    $assertoff;\n"
      "    expect (@(posedge clk) 0) else $display(\"f %0t\", $time);\n"
      "    expect (@(posedge clk) 0);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "f 5\n");
  EXPECT_EQ(ErrorTimes(r.err), "15");
}

TEST(AssertStatusControlSim, AnOnSelectingUnique0ReportsRestoresThemAlone) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  int x = 3, y;\n"
      "  initial begin\n"
      "    $assertcontrol(4, 224);\n"
      "    $assertcontrol(3, 64);\n"
      "    unique if (x == 1) y = 1;\n"
      "    unique0 case (x) 3: y = 2; 3: y = 3; endcase\n"
      "    unique0 if (x == 3) y = 1; else if (x > 2) y = 2;\n"
      "    priority if (x == 1) y = 4;\n"
      "    priority case (x) 1: y = 5; endcase\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.warning_lines, "7 8");
}

TEST(AssertStatusControlSim, AnOnSelectingPriorityReportsRestoresThemAlone) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  int x = 3, y;\n"
      "  initial begin\n"
      "    $assertcontrol(4, 224);\n"
      "    $assertcontrol(3, 128);\n"
      "    unique if (x == 1) y = 1;\n"
      "    unique0 case (x) 3: y = 2; 3: y = 3; endcase\n"
      "    unique0 if (x == 3) y = 1; else if (x > 2) y = 2;\n"
      "    priority if (x == 1) y = 4;\n"
      "    priority case (x) 1: y = 5; endcase\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.warning_lines, "9 10");
}

TEST(AssertStatusControlSim,
     AnOnSelectingOnlyAssertionKindsLeavesViolationReportsOff) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  int x = 3, y;\n"
      "  initial begin\n"
      "    $assertcontrol(4);\n"
      "    $assertcontrol(3, 15);\n"
      "    unique if (x == 1) y = 1;\n"
      "    assert (0);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.warning_lines, "");
  EXPECT_EQ(r.fails, 1);
}

TEST(AssertStatusControlSim, AnOnWithTheExpectBitLeavesAnExpectAsItWas) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  logic clk = 0;\n"
      "  initial repeat (4) #5 clk = ~clk;\n"
      "  initial begin\n"
      "    $assertcontrol(9, 16);\n"
      "    $assertcontrol(3, 16);\n"
      "    expect (@(posedge clk) 0) else $display(\"f %0t\", $time);\n"
      "    $assertcontrol(8, 16);\n"
      "    expect (@(posedge clk) 0) else $display(\"g %0t\", $time);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "g 15\n");
}

TEST(AssertStatusControlSim, UnlockReturnsALockedExpectToActionControl) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  logic clk = 0;\n"
      "  initial repeat (4) #5 clk = ~clk;\n"
      "  initial begin\n"
      "    $assertcontrol(1, 16);\n"
      "    $assertcontrol(9, 16);\n"
      "    expect (@(posedge clk) 0) else $display(\"locked %0t\", $time);\n"
      "    $assertcontrol(2, 16);\n"
      "    $assertcontrol(9, 16);\n"
      "    expect (@(posedge clk) 0) else $display(\"unlocked %0t\", $time);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "locked 5\n");
}

TEST(AssertStatusControlSim, UnlockReturnsLockedViolationReportsToControl) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  int x = 3, y;\n"
      "  initial begin\n"
      "    $assertcontrol(1, 224);\n"
      "    $assertcontrol(4, 224);\n"
      "    unique if (x == 1) y = 1;\n"
      "    unique0 case (x) 3: y = 2; 3: y = 3; endcase\n"
      "    priority if (x == 1) y = 4;\n"
      "    $assertcontrol(2, 224);\n"
      "    $assertcontrol(4, 224);\n"
      "    unique if (x == 1) y = 1;\n"
      "    unique0 case (x) 3: y = 2; 3: y = 3; endcase\n"
      "    priority if (x == 1) y = 4;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.warning_lines, "6 7 8");
}

TEST(AssertStatusControlSim,
     OffAndOnForUnique0StopAndRestoreItsIfAndCaseReports) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  int x = 3, y;\n"
      "  initial begin\n"
      "    $assertcontrol(4, 64);\n"
      "    unique0 if (x == 3) y = 1; else if (x > 2) y = 2;\n"
      "    unique0 case (x) 3: y = 2; 3: y = 3; endcase\n"
      "    $assertcontrol(3, 64);\n"
      "    unique0 if (x == 3) y = 1; else if (x > 2) y = 2;\n"
      "    unique0 case (x) 3: y = 2; 3: y = 3; endcase\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.warning_lines, "8 9");
}

TEST(AssertStatusControlSim,
     OffAndOnForPriorityStopAndRestoreItsIfAndCaseReports) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  int x = 3, y;\n"
      "  initial begin\n"
      "    $assertcontrol(4, 128);\n"
      "    priority if (x == 1) y = 4;\n"
      "    priority case (x) 1: y = 5; endcase\n"
      "    $assertcontrol(3, 128);\n"
      "    priority if (x == 1) y = 4;\n"
      "    priority case (x) 1: y = 5; endcase\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.warning_lines, "8 9");
}

TEST(AssertStatusControlSim, AnOffForUnique0LeavesTheOtherReportsMade) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  int x = 3, y;\n"
      "  initial begin\n"
      "    $assertcontrol(4, 64);\n"
      "    unique if (x == 1) y = 1;\n"
      "    unique0 case (x) 3: y = 2; 3: y = 3; endcase\n"
      "    priority case (x) 1: y = 5; endcase\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.warning_lines, "5 7");
}

TEST(AssertStatusControlSim, AnOffForPriorityLeavesTheOtherReportsMade) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  int x = 3, y;\n"
      "  initial begin\n"
      "    $assertcontrol(4, 128);\n"
      "    unique if (x == 1) y = 1;\n"
      "    unique0 case (x) 3: y = 2; 3: y = 3; endcase\n"
      "    priority case (x) 1: y = 5; endcase\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.warning_lines, "5 6");
}

TEST(AssertStatusControlSim, AKillForUnique0FlushesAQueuedReport) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  int x = 3, y;\n"
      "  initial begin\n"
      "    unique0 case (x) 3: y = 2; 3: y = 3; endcase\n"
      "    $assertcontrol(5, 64);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.warning_lines, "");
}

TEST(AssertStatusControlSim, AKillForPriorityFlushesAQueuedReport) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  int x = 3, y;\n"
      "  initial begin\n"
      "    priority case (x) 1: y = 5; endcase\n"
      "    $assertcontrol(5, 128);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.warning_lines, "");
}

TEST(AssertStatusControlSim, ALockOnBit32HoldsItsReportsAgainstOffAndKill) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  int x = 3, y;\n"
      "  initial begin\n"
      "    $assertcontrol(1, 32);\n"
      "    $assertcontrol(4, 32);\n"
      "    unique if (x == 1) y = 1;\n"
      "    $assertcontrol(5, 32);\n"
      "    $assertcontrol(2, 32);\n"
      "    $assertcontrol(4, 32);\n"
      "    unique if (x == 1) y = 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.warning_lines, "6");
}

TEST(AssertStatusControlSim, ALockOnBit64HoldsItsReportsAgainstOffAndKill) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  int x = 3, y;\n"
      "  initial begin\n"
      "    $assertcontrol(1, 64);\n"
      "    $assertcontrol(4, 64);\n"
      "    unique0 case (x) 3: y = 2; 3: y = 3; endcase\n"
      "    $assertcontrol(5, 64);\n"
      "    $assertcontrol(2, 64);\n"
      "    $assertcontrol(4, 64);\n"
      "    unique0 case (x) 3: y = 2; 3: y = 3; endcase\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.warning_lines, "6");
}

TEST(AssertStatusControlSim, ALockOnBit128HoldsItsReportsAgainstOffAndKill) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  int x = 3, y;\n"
      "  initial begin\n"
      "    $assertcontrol(1, 128);\n"
      "    $assertcontrol(4, 128);\n"
      "    priority case (x) 1: y = 5; endcase\n"
      "    $assertcontrol(5, 128);\n"
      "    $assertcontrol(2, 128);\n"
      "    $assertcontrol(4, 128);\n"
      "    priority case (x) 1: y = 5; endcase\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.warning_lines, "6");
}

TEST(AssertStatusControlSim, AViolationInAFunctionBodyObeysTheControls) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  int x = 3, y;\n"
      "  function void pick();\n"
      "    unique if (x == 1) y = 1;\n"
      "  endfunction\n"
      "  initial begin\n"
      "    pick();\n"
      "    $assertcontrol(4, 32);\n"
      "    pick();\n"
      "    $assertcontrol(3, 32);\n"
      "    pick();\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.warnings, 2u);
}

TEST(AssertStatusControlSim,
     AssertionTypeBit4AloneSelectsObservedDeferredAssertions) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  initial begin\n"
      "    $assertcontrol(4, 4);\n"
      "    assert (0) else $display(\"simple\");\n"
      "    assert #0 (0) else $display(\"observed\");\n"
      "    assert final (0) else $display(\"final\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "simple\nfinal\n");
}

TEST(AssertStatusControlSim,
     AssertionTypeBit8AloneSelectsFinalDeferredAssertions) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  initial begin\n"
      "    $assertcontrol(4, 8);\n"
      "    assert (0) else $display(\"simple\");\n"
      "    assert #0 (0) else $display(\"observed\");\n"
      "    assert final (0) else $display(\"final\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "simple\nobserved\n");
}

TEST(AssertStatusControlSim, AssertionTypeBit16SelectsExpectStatements) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  logic clk = 0;\n"
      "  initial repeat (2) #5 clk = ~clk;\n"
      "  initial begin\n"
      "    $assertcontrol(9, 16);\n"
      "    assert (0) else $display(\"simple\");\n"
      "    expect (@(posedge clk) 0) else $display(\"expect\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "simple\n");
}

TEST(AssertStatusControlSim,
     AssertionTypeBit64SelectsUnique0ReportsAndLeavesUnique) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  int x = 3, y;\n"
      "  initial begin\n"
      "    $assertcontrol(4, 64);\n"
      "    unique if (x == 1) y = 1;\n"
      "    unique0 if (x == 3) y = 1; else if (x > 2) y = 2;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.warning_lines, "5");
}

TEST(AssertStatusControlSim,
     AssertionTypeBit128SelectsPriorityIfAndCaseReports) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  int x = 3, y;\n"
      "  initial begin\n"
      "    $assertcontrol(4, 128);\n"
      "    unique case (x) 1: y = 6; endcase\n"
      "    priority if (x == 1) y = 4;\n"
      "    priority case (x) 1: y = 5; endcase\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.warning_lines, "5");
}

TEST(AssertStatusControlSim, AnOrOfAssertionTypeBitsActsOnEachNamedKind) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  logic clk = 0;\n"
      "  initial repeat (2) #5 clk = ~clk;\n"
      "  c1: assert property (@(posedge clk) 0) else "
      "$display(\"concurrent\");\n"
      "  initial begin\n"
      "    $assertcontrol(4, 3);\n"
      "    assert (0) else $display(\"simple\");\n"
      "    assert #0 (0) else $display(\"observed\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "observed\n");
}

TEST(AssertStatusControlSim, AssertionType96SelectsUniqueAndUnique0Reports) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  int x = 3, y;\n"
      "  initial begin\n"
      "    $assertcontrol(4, 96);\n"
      "    unique if (x == 1) y = 1;\n"
      "    unique0 case (x) 3: y = 2; 3: y = 3; endcase\n"
      "    priority if (x == 1) y = 4;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.warning_lines, "7");
}

TEST(AssertStatusControlSim, AnOmittedAssertionTypeReachesViolationReports) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  int x = 3, y;\n"
      "  initial begin\n"
      "    $assertcontrol(4);\n"
      "    unique if (x == 1) y = 1;\n"
      "    unique0 case (x) 3: y = 2; 3: y = 3; endcase\n"
      "    priority if (x == 1) y = 4;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.warning_lines, "");
}

TEST(AssertStatusControlSim, AnOmittedAssertionTypeReachesExpect) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  logic clk = 0;\n"
      "  initial repeat (2) #5 clk = ~clk;\n"
      "  initial begin\n"
      "    $assertcontrol(9);\n"
      "    expect (@(posedge clk) 0) else $display(\"expect\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "");
}

TEST(AssertStatusControlSim, DirectiveType4AloneSelectsAssume) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  initial begin\n"
      "    $assertcontrol(4, 255, 4);\n"
      "    assume (0) else $display(\"assume\");\n"
      "    assert (0) else $display(\"assert\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "assert\n");
}

TEST(AssertStatusControlSim, DirectiveType1AloneSelectsAssert) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  initial begin\n"
      "    $assertcontrol(4, 255, 1);\n"
      "    assert (0) else $display(\"assert\");\n"
      "    cover (1);\n"
      "    assume (0) else $display(\"assume\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "assume\n");
  EXPECT_EQ(r.cover_evaluated, 1u);
}

TEST(AssertStatusControlSim, DirectiveType3SelectsAssertAndCover) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  initial begin\n"
      "    $assertcontrol(4, 255, 3);\n"
      "    assert (0) else $display(\"assert\");\n"
      "    cover (1);\n"
      "    assume (0) else $display(\"assume\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "assume\n");
  EXPECT_EQ(r.cover_evaluated, 0u);
}

TEST(AssertStatusControlSim, DirectiveType6LeavesAssertChecked) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  initial begin\n"
      "    $assertcontrol(4, 255, 6);\n"
      "    assert (0) else $display(\"assert\");\n"
      "    cover (1);\n"
      "    assume (0) else $display(\"assume\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "assert\n");
  EXPECT_EQ(r.cover_evaluated, 0u);
}

TEST(AssertStatusControlSim, DirectiveTypeSelectsConcurrentCoverAndAssume) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  logic clk = 0;\n"
      "  initial repeat (6) #5 clk = ~clk;\n"
      "  a1: assert property (@(posedge clk) 0) else $display(\"assert %0t\", "
      "$time);\n"
      "  m1: assume property (@(posedge clk) 0) else $display(\"assume %0t\", "
      "$time);\n"
      "  c1: cover property (@(posedge clk) 1) $display(\"cover %0t\", "
      "$time);\n"
      "  initial begin\n"
      "    #10 $assertcontrol(4, 255, 2);\n"
      "    #10 $assertcontrol(3);\n"
      "    $assertcontrol(4, 255, 4);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out,
            "assert 5\nassume 5\ncover 5\nassert 15\nassume 15\nassert "
            "25\ncover 25\n");
}

TEST(AssertStatusControlSim, DirectiveTypeIsIgnoredForViolationReports) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  int x = 3, y;\n"
      "  initial begin\n"
      "    $assertcontrol(4, 32, 2);\n"
      "    unique if (x == 1) y = 1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.warning_lines, "");
}

TEST(AssertStatusControlSim, DirectiveTypeIsIgnoredForExpect) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  logic clk = 0;\n"
      "  initial repeat (2) #5 clk = ~clk;\n"
      "  initial begin\n"
      "    $assertcontrol(9, 16, 2);\n"
      "    expect (@(posedge clk) 0) else $display(\"expect\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "");
}

TEST(AssertStatusControlSim, ANamedCoverOutsideTheDirectiveTypeIsLeftAlone) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  initial begin\n"
      "    $assertcontrol(4, 255, 1, 0, c1);\n"
      "    c1: cover (1);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.cover_evaluated, 1u);
}

TEST(AssertStatusControlSim, AnActionTaskTakesLevelsAndAList) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  initial begin\n"
      "    $assertpassoff(0);\n"
      "    assert (1) $display(\"pass\");\n"
      "    $assertpasson;\n"
      "    $assertfailoff(0, a1);\n"
      "    a1: assert (0) else $display(\"a1\");\n"
      "    a2: assert (0) else $display(\"a2\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "a2\n");
}

TEST(AssertStatusControlSim, AnEmptyAssertionTypeTakesItsDefault) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  initial begin\n"
      "    $assertcontrol(4, , 2);\n"
      "    assert (0) else $display(\"assert\");\n"
      "    cover (1);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "assert\n");
  EXPECT_EQ(r.cover_evaluated, 0u);
}

TEST(AssertStatusControlSim, EmptyArgumentsBeforeTheListTakeTheirDefaults) {
  ControlRun r = RunControlled(
      "module sub;\n"
      "  initial assert final (0) else $display(\"sub\");\n"
      "endmodule\n"
      "module t;\n"
      "  sub m();\n"
      "  initial begin\n"
      "    $assertcontrol(4,,,,t.m);\n"
      "    assert final (0) else $display(\"top\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "top\n");
}

TEST(AssertStatusControlSim, ALetConstantControlTypeHasTheEffectOfItsValue) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  let OFF = 4;\n"
      "  let ON = 3;\n"
      "  initial begin\n"
      "    $assertcontrol(OFF);\n"
      "    assert (0) else $display(\"off\");\n"
      "    $assertcontrol(ON);\n"
      "    assert (0) else $display(\"on\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "on\n");
}

TEST(AssertStatusControlSim,
     AVariableControlTypeHasTheEffectOfItsCurrentValue) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  int c;\n"
      "  initial begin\n"
      "    c = 4;\n"
      "    $assertcontrol(c);\n"
      "    assert (0) else $display(\"off\");\n"
      "    c = 3;\n"
      "    $assertcontrol(c);\n"
      "    assert (0) else $display(\"on\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(r.out, "on\n");
}

}  // namespace
