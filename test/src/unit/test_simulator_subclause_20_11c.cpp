#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>

#include "helpers_assert_control_runs.h"
#include "simulator/sva_engine_queues.h"

using namespace delta;

namespace {

TEST(AssertActionControlSim, AVacuousSuccessRunsThePassActionWithNoControl) {
  EXPECT_EQ(ControlledOutput("module t;\n"
                             "  logic clk = 0;\n"
                             "  initial repeat (4) #5 clk = ~clk;\n"
                             "  bit a = 0, b = 0;\n"
                             "  assert property (@(posedge clk) a |-> b) "
                             "$display(\"pass %0t\", $time);\n"
                             "    else $display(\"fail %0t\", $time);\n"
                             "endmodule\n"),
            "pass 5\npass 15\n");
}

TEST(AssertActionControlSim, PassOffStopsBothSuccessesAndPassOnRestoresThem) {
  EXPECT_EQ(ControlledOutput("module t;\n"
                             "  logic clk = 0;\n"
                             "  initial repeat (12) #5 clk = ~clk;\n"
                             "  bit a = 0, b = 1;\n"
                             "  av: assert property (@(posedge clk) a |-> b) "
                             "$display(\"v %0t\", $time);\n"
                             "  an: assert property (@(posedge clk) b |-> b) "
                             "$display(\"n %0t\", $time);\n"
                             "  initial begin\n"
                             "    #10 $assertpassoff;\n"
                             "    #20 $assertpasson;\n"
                             "    #10 $assertpassoff;\n"
                             "    #1 $assertnonvacuouson;\n"
                             "  end\n"
                             "endmodule\n"),
            "v 5\nn 5\nv 35\nn 35\nn 45\nn 55\n");
}

TEST(AssertActionControlSim, PassOffAndPassOnActOnDeferredAssertions) {
  EXPECT_EQ(ControlledOutput("module t;\n"
                             "  initial begin\n"
                             "    $assertpassoff;\n"
                             "    assert #0 (1) $display(\"observed off\");\n"
                             "    assert final (1) $display(\"final off\");\n"
                             "    #1 $assertpasson;\n"
                             "    assert #0 (1) $display(\"observed on\");\n"
                             "    assert final (1) $display(\"final on\");\n"
                             "  end\n"
                             "endmodule\n"),
            "observed on\nfinal on\n");
}

TEST(AssertActionControlSim, PassOffAndPassOnActOnExpect) {
  EXPECT_EQ(ControlledOutput(
                "module t;\n"
                "  logic clk = 0;\n"
                "  initial repeat (6) #5 clk = ~clk;\n"
                "  initial begin\n"
                "    $assertpassoff;\n"
                "    expect (@(posedge clk) 1) $display(\"off %0t\", $time);\n"
                "    $assertpasson;\n"
                "    expect (@(posedge clk) 1) $display(\"on %0t\", $time);\n"
                "  end\n"
                "endmodule\n"),
            "on 15\n");
}

TEST(AssertActionControlSim, VacuousOffStopsOnlyTheVacuousPassUntilPassOn) {
  EXPECT_EQ(ControlledOutput("module t;\n"
                             "  logic clk = 0;\n"
                             "  initial repeat (8) #5 clk = ~clk;\n"
                             "  bit a = 0, b = 1;\n"
                             "  av: assert property (@(posedge clk) a |-> b) "
                             "$display(\"v %0t\", $time);\n"
                             "  an: assert property (@(posedge clk) b |-> b) "
                             "$display(\"n %0t\", $time);\n"
                             "  initial begin\n"
                             "    #10 $assertvacuousoff;\n"
                             "    #20 $assertpasson;\n"
                             "  end\n"
                             "endmodule\n"),
            "v 5\nn 5\nn 15\nn 25\nv 35\nn 35\n");
}

constexpr const char* kPassOffThenNonvacuousOn[] = {
    "    #10 $assertpassoff;\n"
    "    #1 $assertnonvacuouson;\n",
    "    #10 $assertcontrol(7);\n"
    "    #1 $assertcontrol(10);\n"};

TEST(AssertActionControlSim,
     NonvacuousOnAfterPassOffRestoresOnlyTheNonvacuousPass) {
  for (const char* controls : kPassOffThenNonvacuousOn) {
    std::string src =
        "module t;\n"
        "  logic clk = 0;\n"
        "  initial repeat (6) #5 clk = ~clk;\n"
        "  bit a = 0, b = 1;\n"
        "  av: assert property (@(posedge clk) a |-> b) $display(\"v %0t\", "
        "$time);\n"
        "  an: assert property (@(posedge clk) b |-> b) $display(\"n %0t\", "
        "$time);\n"
        "  initial begin\n";
    src += controls;
    src += "  end\nendmodule\n";
    EXPECT_EQ(ControlledOutput(src), "v 5\nn 5\nn 15\nn 25\n") << controls;
  }
}

TEST(AssertActionControlSim, DISABLED_VacuousOffAndNonvacuousOnActOnExpect) {
  EXPECT_EQ(ControlledOutput("module t;\n"
                             "  logic clk = 0;\n"
                             "  initial repeat (8) #5 clk = ~clk;\n"
                             "  initial begin\n"
                             "    $assertvacuousoff;\n"
                             "    expect (@(posedge clk) 0 |-> 1) "
                             "$display(\"vacuous %0t\", $time);\n"
                             "    expect (@(posedge clk) 1 |-> 1) "
                             "$display(\"nonvacuous %0t\", $time);\n"
                             "    $assertpassoff;\n"
                             "    $assertnonvacuouson;\n"
                             "    expect (@(posedge clk) 1 |-> 1) "
                             "$display(\"restored %0t\", $time);\n"
                             "    expect (@(posedge clk) 0 |-> 1) "
                             "$display(\"still off %0t\", $time);\n"
                             "  end\n"
                             "endmodule\n"),
            "nonvacuous 15\nrestored 25\n");
}

TEST(AssertActionControlSim,
     FailOffStopsTheDefaultErrorOfAConcurrentAssertAndAssume) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  logic clk = 0;\n"
      "  initial repeat (8) #5 clk = ~clk;\n"
      "  a1: assert property (@(posedge clk) 0);\n"
      "  m1: assume property (@(posedge clk) 0);\n"
      "  initial begin\n"
      "    #10 $assertfailoff;\n"
      "    #20 $assertfailon;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(ErrorTimes(r.err), "5 5 35 35");
}

TEST(AssertActionControlSim, FailOffStopsTheDefaultErrorOfAnExpect) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  logic clk = 0;\n"
      "  initial repeat (4) #5 clk = ~clk;\n"
      "  initial begin\n"
      "    $assertfailoff;\n"
      "    expect (@(posedge clk) 0);\n"
      "    $assertfailon;\n"
      "    expect (@(posedge clk) 0);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(ErrorTimes(r.err), "15");
}

TEST(AssertActionControlSim,
     FailOffStopsTheElseOfAConcurrentAssertionUntilFailOn) {
  EXPECT_EQ(ControlledOutput("module t;\n"
                             "  logic clk = 0;\n"
                             "  initial repeat (8) #5 clk = ~clk;\n"
                             "  assert property (@(posedge clk) 0) else "
                             "$display(\"f %0t\", $time);\n"
                             "  initial begin\n"
                             "    #10 $assertfailoff;\n"
                             "    #20 $assertfailon;\n"
                             "  end\n"
                             "endmodule\n"),
            "f 5\nf 35\n");
}

TEST(AssertActionControlSim, FailOffStopsTheElseOfAnExpectUntilFailOn) {
  EXPECT_EQ(
      ControlledOutput(
          "module t;\n"
          "  logic clk = 0;\n"
          "  initial repeat (4) #5 clk = ~clk;\n"
          "  initial begin\n"
          "    $assertfailoff;\n"
          "    expect (@(posedge clk) 0) else $display(\"off %0t\", $time);\n"
          "    $assertfailon;\n"
          "    expect (@(posedge clk) 0) else $display(\"on %0t\", $time);\n"
          "  end\n"
          "endmodule\n"),
      "on 15\n");
}

TEST(AssertActionControlSim, FailOffAndFailOnActOnDeferredAssertions) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  initial begin\n"
      "    $assertfailoff;\n"
      "    assert #0 (0) else $display(\"observed off\");\n"
      "    assert final (0) else $display(\"final off\");\n"
      "    assert #0 (0);\n"
      "    assert final (0);\n"
      "    #1 $assertfailon;\n"
      "    assert #0 (0) else $display(\"observed on\");\n"
      "    assert final (0) else $display(\"final on\");\n"
      "    assert #0 (0);\n"
      "    assert final (0);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(ErrorTimes(r.err), "1 1");
  EXPECT_EQ(r.out, "observed on\nfinal on\n");
}

TEST(AssertActionControlSim, FailOffAndFailOnActOnAnImmediateAssume) {
  ControlRun r = RunControlled(
      "module t;\n"
      "  initial begin\n"
      "    $assertfailoff;\n"
      "    assume (0) else $display(\"off\");\n"
      "    assume (0);\n"
      "    $assertfailon;\n"
      "    assume (0) else $display(\"on\");\n"
      "    assume (0);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(ErrorTimes(r.err), "0");
  EXPECT_EQ(r.out, "on\n");
}

constexpr std::pair<const char*, AssertControlType> kActionTasks[] = {
    {"$assertpasson", AssertControlType::kPassOn},
    {"$assertpassoff", AssertControlType::kPassOff},
    {"$assertfailon", AssertControlType::kFailOn},
    {"$assertfailoff", AssertControlType::kFailOff},
    {"$assertnonvacuouson", AssertControlType::kNonvacuousOn},
    {"$assertvacuousoff", AssertControlType::kVacuousOff}};

TEST(AssertActionControlSim,
     EveryActionTaskExpandsWithAssertionType31AndDirectiveType7) {
  for (const auto& [task, control] : kActionTasks) {
    AssertControlInvocation inv;
    ASSERT_TRUE(EquivalentAssertControlForTask(task, inv)) << task;
    EXPECT_EQ(inv.control_type, static_cast<uint32_t>(control)) << task;
    EXPECT_EQ(inv.assertion_type, 31u) << task;
    EXPECT_EQ(inv.directive_type, 7u) << task;
  }
}

constexpr const char* kFailOffInSub[] = {"$assertfailoff(0, u);",
                                         "$assertcontrol(9, 31, 7, 0, u);"};

TEST(AssertActionControlSim, AnActionTaskListSelectsAsItsAssertControlDoes) {
  for (const char* control : kFailOffInSub) {
    std::string src =
        "module sub;\n"
        "  initial #1 assert (0) else $display(\"sub fail\");\n"
        "endmodule\n"
        "module t;\n"
        "  sub u();\n"
        "  initial begin\n"
        "    ";
    src += control;
    src +=
        "\n"
        "    #1 assert (0) else $display(\"top fail\");\n"
        "  end\n"
        "endmodule\n";
    EXPECT_EQ(ControlledOutput(src), "top fail\n") << control;
  }
}

TEST(AssertActionControlSim, DISABLED_EveryActionTaskReachesAnExpect) {
  EXPECT_EQ(
      ControlledOutput(
          "module t;\n"
          "  logic clk = 0;\n"
          "  initial repeat (12) #5 clk = ~clk;\n"
          "  initial begin\n"
          "    $assertpassoff;\n"
          "    expect (@(posedge clk) 1) $display(\"passoff %0t\", $time);\n"
          "    $assertpasson;\n"
          "    expect (@(posedge clk) 1) $display(\"passon %0t\", $time);\n"
          "    $assertfailoff;\n"
          "    expect (@(posedge clk) 0) else $display(\"failoff %0t\", "
          "$time);\n"
          "    $assertfailon;\n"
          "    expect (@(posedge clk) 0) else $display(\"failon %0t\", "
          "$time);\n"
          "    $assertvacuousoff;\n"
          "    expect (@(posedge clk) 0 |-> 1) $display(\"vacuousoff %0t\", "
          "$time);\n"
          "    $assertpassoff;\n"
          "    $assertnonvacuouson;\n"
          "    expect (@(posedge clk) 1 |-> 1) $display(\"nonvacuouson %0t\", "
          "$time);\n"
          "  end\n"
          "endmodule\n"),
      "passon 15\nfailon 35\nnonvacuouson 55\n");
}

TEST(AssertActionControlSim, EveryActionTaskLeavesViolationReportsMade) {
  for (const auto& [task, control] : kActionTasks) {
    std::string src =
        "module t;\n"
        "  int x = 3, y;\n"
        "  initial begin\n"
        "    ";
    src += task;
    src +=
        ";\n"
        "    unique if (x == 1) y = 1;\n"
        "    unique0 case (x) 3: y = 2; 3: y = 3; endcase\n"
        "    priority if (x == 1) y = 4;\n"
        "  end\n"
        "endmodule\n";
    EXPECT_EQ(RunControlled(src).warnings, 3u) << task;
  }
}

constexpr const char* kViolationReportMasks[] = {
    "$assertcontrol(9);", "$assertcontrol(7, 224);", "$assertcontrol(11, 32);"};

TEST(AssertActionControlSim,
     AnActionControlSelectingViolationReportsLeavesThemMade) {
  for (const char* control : kViolationReportMasks) {
    std::string src =
        "module t;\n"
        "  int x = 3, y;\n"
        "  initial begin\n"
        "    ";
    src += control;
    src +=
        "\n"
        "    unique if (x == 1) y = 1;\n"
        "  end\n"
        "endmodule\n";
    EXPECT_EQ(RunControlled(src).warnings, 1u) << control;
  }
}

constexpr const char* kFailOffThenOn[] = {
    "    $assertfailoff;\n    assert (0);\n    $assertfailon;\n",
    "    $assertcontrol(9);\n    assert (0);\n    $assertcontrol(8);\n"};

TEST(AssertActionControlSim, FailOnLeavesTheFailureCountAsItWas) {
  for (const char* controls : kFailOffThenOn) {
    std::string src = "module t;\n  initial begin\n";
    src += controls;
    src += "    assert (0);\n  end\nendmodule\n";
    EXPECT_EQ(RunControlled(src).fails, 2) << controls;
  }
}

constexpr const char* kPassOffForms[] = {
    "$assertpassoff;", "$assertcontrol(7);", "$assertvacuousoff;",
    "$assertcontrol(11);"};

TEST(AssertActionControlSim, ACoverIsStillCountedUnderAPassActionControl) {
  for (const char* control : kPassOffForms) {
    std::string src =
        "module t;\n"
        "  logic clk = 0;\n"
        "  initial repeat (4) #5 clk = ~clk;\n"
        "  c1: cover property (@(posedge clk) 1) $display(\"c1\");\n"
        "  initial begin\n"
        "    ";
    src += control;
    src +=
        "\n"
        "    cover (1) $display(\"ci\");\n"
        "  end\n"
        "endmodule\n";
    ControlRun r = RunControlled(src);
    EXPECT_EQ(r.cover_succeeded, 3u) << control;
  }
}

TEST(AssertActionControlSim,
     DISABLED_AnActionControlLeavesAnAttemptAlreadyInFlight) {
  EXPECT_EQ(ControlledOutput("module t;\n"
                             "  logic clk = 0;\n"
                             "  initial repeat (8) #5 clk = ~clk;\n"
                             "  assert property (@(posedge clk) 1 |-> ##2 0)\n"
                             "    else $display(\"f %0t\", $time);\n"
                             "  initial #10 $assertfailoff;\n"
                             "endmodule\n"),
            "f 25\n");
}

}  // namespace
