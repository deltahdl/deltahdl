#include <gtest/gtest.h>

#include <array>
#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "helpers_assertion_control_table.h"
#include "helpers_assertion_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

std::vector<Op> OnEach(int arm, int operation, const char* instance = kU1,
                       int result = 1) {
  constexpr std::array<const char*, 6> kNames = {"an",  "av",  "af",
                                                 "amf", "amn", "amv"};
  std::vector<Op> ops;
  ops.reserve(kNames.size());
  for (const char* name : kNames) {
    ops.push_back({arm, operation, std::string(instance) + "." + name, result});
  }
  return ops;
}

std::vector<Op> Join(std::vector<std::vector<Op>> parts) {
  std::vector<Op> ops;
  for (std::vector<Op>& part : parts) {
    ops.insert(ops.end(), part.begin(), part.end());
  }
  return ops;
}

ControlRun OnU1(const char* name, std::vector<std::vector<Op>> parts, Counts u1,
                std::vector<uint64_t> failures) {
  return {name, Join(std::move(parts)), u1, kUncontrolled, std::move(failures)};
}

class AssertionControlRun : public ControlTableRun {};

TEST_P(AssertionControlRun, ControlsActOnTheirAssertionFromTheirTimeOn) {
  RunRow();
  ExpectSettled();
}

class InFlightAssertionControlRun : public ControlTableRun {};

TEST_P(InFlightAssertionControlRun, AnAttemptInFlightMeetsOnlyAReset) {
  RunRow();
  ExpectInFlight();
}

std::vector<ControlRun> StateControls() {
  return {
      OnU1("NoControl", {}, kUncontrolled, EveryFailure()),
      OnU1("DisableThenEnable",
           {OnEach(1, vpiAssertionDisable), OnEach(2, vpiAssertionEnable)},
           kOffUntilTheSecondArm, {25, 35}),
      OnU1("DisableTwiceThenEnableOnce",
           {OnEach(1, vpiAssertionDisable), OnEach(2, vpiAssertionDisable),
            OnEach(3, vpiAssertionEnable)},
           {40, 40, 40, 15, 25, 25}, {35}),
      OnU1("EnableWhileEnabled",
           {OnEach(1, vpiAssertionEnable), OnEach(2, vpiAssertionDisable),
            OnEach(3, vpiAssertionEnable)},
           {55, 55, 55, 40, 60, 60}, {15, 35}),
      OnU1("DisableThenReset",
           {OnEach(1, vpiAssertionDisable), OnEach(2, vpiAssertionReset)},
           {65, 65, 65, 50, 0, 0}, {25, 35}),
      OnU1("Reset", {OnEach(1, vpiAssertionReset)}, {80, 80, 80, 60, 35, 35},
           EveryFailure()),
      OnU1("LockRefusesDisableAndResetUntilUnlock",
           {OnEach(1, vpiAssertionLock), OnEach(1, vpiAssertionDisable, kU1, 0),
            OnEach(1, vpiAssertionReset, kU1, 0), OnEach(2, vpiAssertionUnlock),
            OnEach(2, vpiAssertionDisable)},
           kOffFromTheSecondArm, {15}),
      ControlRun{"ALockLeavesTheOtherAssertionsControllable",
                 Join({OnEach(1, vpiAssertionLock),
                       OnEach(1, vpiAssertionDisable, kU2)}),
                 kUncontrolled, kOffFromTheFirstArm, EveryFailure()},
  };
}

std::vector<ControlRun> ActionControls() {
  return {
      OnU1("PassActionOffThenOn",
           {OnEach(1, vpiAssertionDisablePassAction),
            OnEach(2, vpiAssertionEnablePassAction)},
           {65, 65, 80, 75, 25, 25}, EveryFailure()),
      OnU1("PassActionOffTwiceThenOnOnce",
           {OnEach(1, vpiAssertionDisablePassAction),
            OnEach(2, vpiAssertionDisablePassAction),
            OnEach(3, vpiAssertionEnablePassAction)},
           {40, 40, 80, 75, 25, 25}, EveryFailure()),
      OnU1("PassActionOnWhileOn",
           {OnEach(1, vpiAssertionEnablePassAction),
            OnEach(2, vpiAssertionDisablePassAction),
            OnEach(3, vpiAssertionEnablePassAction)},
           {55, 55, 80, 75, 60, 60}, EveryFailure()),
      OnU1("VacuousActionOff", {OnEach(1, vpiAssertionDisableVacuousAction)},
           kVacuousOffFromTheFirstArm, EveryFailure()),
      OnU1("PassActionOffThenNonvacuousOn",
           {OnEach(1, vpiAssertionDisablePassAction),
            OnEach(2, vpiAssertionEnableNonvacuousAction)},
           {65, 5, 80, 75, 25, 25}, EveryFailure()),
      OnU1("VacuousActionOffTwiceThenPassOn",
           {OnEach(1, vpiAssertionDisableVacuousAction),
            OnEach(2, vpiAssertionDisableVacuousAction),
            OnEach(3, vpiAssertionEnablePassAction)},
           {80, 40, 80, 75, 60, 25}, EveryFailure()),
      OnU1("NonvacuousActionOnTwice",
           {OnEach(1, vpiAssertionDisablePassAction),
            OnEach(2, vpiAssertionEnableNonvacuousAction),
            OnEach(3, vpiAssertionEnableNonvacuousAction)},
           {65, 5, 80, 75, 25, 25}, EveryFailure()),
      OnU1("FailActionOffThenOn",
           {OnEach(1, vpiAssertionDisableFailAction),
            OnEach(2, vpiAssertionEnableFailAction)},
           {80, 80, 65, 50, 60, 60}, EveryFailure()),
      OnU1("FailActionOffTwiceThenOnOnce",
           {OnEach(1, vpiAssertionDisableFailAction),
            OnEach(2, vpiAssertionDisableFailAction),
            OnEach(3, vpiAssertionEnableFailAction)},
           {80, 80, 40, 15, 60, 60}, EveryFailure()),
      OnU1("FailActionOnWhileOn",
           {OnEach(1, vpiAssertionEnableFailAction),
            OnEach(2, vpiAssertionDisableFailAction),
            OnEach(3, vpiAssertionEnableFailAction)},
           {80, 80, 55, 40, 60, 60}, EveryFailure()),
      OnU1("ActionsOffThenReset",
           {OnEach(1, vpiAssertionDisablePassAction),
            OnEach(2, vpiAssertionDisableFailAction),
            OnEach(3, vpiAssertionReset)},
           {40, 40, 55, 40, 25, 25}, EveryFailure()),
      OnU1("LockRefusesActionControlsUntilUnlock",
           {OnEach(1, vpiAssertionLock),
            OnEach(1, vpiAssertionDisablePassAction, kU1, 0),
            OnEach(1, vpiAssertionDisableFailAction, kU1, 0),
            OnEach(1, vpiAssertionDisableVacuousAction, kU1, 0),
            OnEach(1, vpiAssertionEnablePassAction, kU1, 0),
            OnEach(1, vpiAssertionEnableFailAction, kU1, 0),
            OnEach(1, vpiAssertionEnableNonvacuousAction, kU1, 0),
            OnEach(2, vpiAssertionUnlock),
            OnEach(2, vpiAssertionDisableFailAction)},
           {80, 80, 20, 40, 60, 60}, EveryFailure()),
  };
}

INSTANTIATE_TEST_SUITE_P(StateControls, AssertionControlRun,
                         ::testing::ValuesIn(StateControls()), RowName);
INSTANTIATE_TEST_SUITE_P(ActionControls, AssertionControlRun,
                         ::testing::ValuesIn(ActionControls()), RowName);
INSTANTIATE_TEST_SUITE_P(StateControls, InFlightAssertionControlRun,
                         ::testing::ValuesIn(StateControls()), RowName);
INSTANTIATE_TEST_SUITE_P(DISABLED_ActionControls, InFlightAssertionControlRun,
                         ::testing::ValuesIn(ActionControls()), RowName);

struct Kind {
  const char* name;
  int reason;
};

class AssertionKindRun : public AssertionRun,
                         public ::testing::WithParamInterface<Kind> {};

TEST_P(AssertionKindRun, EachAssertionStatementIsControlledThroughItsHandle) {
  Kind kind = GetParam();
  ArmInTurn(
      {[kind] { ASSERT_NE(WatchAssertion(kind.name, kind.reason), nullptr); },
       [kind] {
         EXPECT_EQ(vpi_control(vpiAssertionDisable,
                               vpi_handle_by_name(VpiText(kind.name), nullptr)),
                   1);
       }});
  testing::internal::CaptureStderr();
  Run("interface bus(input logic clk);\n"
      "  logic a = 0;\n"
      "  ai: assert property (@(posedge clk) a);\n"
      "endinterface\n"
      "program prg(input logic clk);\n"
      "  logic a = 0;\n"
      "  ap: assert property (@(posedge clk) a);\n"
      "endprogram\n"
      "checker chk(logic clk, logic a);\n"
      "  ac: assert property (@(posedge clk) a);\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk = 0, a = 0, b = 1;\n"
      "  always #5 clk = ~clk;\n"
      "  bus i(clk);\n"
      "  prg p(clk);\n"
      "  chk ck(clk, a);\n"
      "  sm: assume property (@(posedge clk) a);\n"
      "  sc: cover property (@(posedge clk) b);\n"
      "  always @(posedge clk) begin\n"
      "    ia: assert (a);\n"
      "    im: assume (a);\n"
      "    ic: cover (b);\n"
      "    da: assert #0 (a);\n"
      "    dm: assume #0 (a);\n"
      "    dc: cover #0 (b);\n"
      "    fa: assert final (a);\n"
      "    fm: assume final (a);\n"
      "    fc: cover final (b);\n"
      "  end\n"
      "  initial begin $arm; #10 $arm; #20 $finish; end\n"
      "endmodule\n");
  testing::internal::GetCapturedStderr();

  std::vector<uint64_t> times;
  for (const AssertionCall& call : CallsOf(kind.reason)) {
    times.push_back(call.cb_time);
  }
  EXPECT_EQ(times, (std::vector<uint64_t>{5}));
}

INSTANTIATE_TEST_SUITE_P(
    EachKind, AssertionKindRun,
    ::testing::Values(
        Kind{"top.i.ai", cbAssertionFailure},
        Kind{"top.p.ap", cbAssertionFailure},
        Kind{"top.ck.ac", cbAssertionFailure},
        Kind{"top.sm", cbAssertionFailure}, Kind{"top.sc", cbAssertionSuccess},
        Kind{"top.ia", cbAssertionFailure}, Kind{"top.im", cbAssertionFailure},
        Kind{"top.ic", cbAssertionSuccess}, Kind{"top.da", cbAssertionFailure},
        Kind{"top.dm", cbAssertionFailure}, Kind{"top.dc", cbAssertionSuccess},
        Kind{"top.fa", cbAssertionFailure}, Kind{"top.fm", cbAssertionFailure},
        Kind{"top.fc", cbAssertionSuccess}),
    [](const ::testing::TestParamInfo<Kind>& info) {
      std::string name = info.param.name;
      return name.substr(name.rfind('.') + 1);
    });

constexpr const char* kFailingWithObjects =
    "module top;\n"
    "  logic clk = 0, a = 0, v = 0;\n"
    "  wire w = 0;\n"
    "  int f = 0;\n"
    "  always #5 clk = ~clk;\n"
    "  a1: assert property (@(posedge clk) a) else f++;\n"
    "  rs: restrict property (@(posedge clk) a);\n"
    "  initial begin #10 $arm; #20 $finish; end\n"
    "endmodule\n";

TEST_F(AssertionRun, AHandleOfAnotherObjectIsRefused) {
  ArmInTurn({[] {
    for (const char* name : {"top", "top.w", "top.v"}) {
      EXPECT_EQ(vpi_control(vpiAssertionDisable,
                            vpi_handle_by_name(VpiText(name), nullptr)),
                0)
          << name;
    }
  }});
  Run(kFailingWithObjects);

  EXPECT_EQ(IntOf("top.f"), 3);
}

TEST_F(AssertionRun, ARestrictIsControlledThroughItsHandle) {
  ArmInTurn({[] {
    EXPECT_EQ(vpi_control(vpiAssertionDisable,
                          vpi_handle_by_name(VpiText("top.rs"), nullptr)),
              1);
  }});
  Run(kFailingWithObjects);

  EXPECT_EQ(IntOf("top.f"), 3);
}

TEST_F(AssertionRun, AKillKeepsThePastValuesSampledBeforeIt) {
  ArmInTurn({[] {
    s_vpi_time start = {vpiSimTime, 0, 5, 0.0};
    EXPECT_EQ(
        vpi_control(vpiAssertionKill,
                    vpi_handle_by_name(VpiText("top.a1"), nullptr), &start),
        1);
  }});
  Run("module top;\n"
      "  logic clk = 0, x = 1;\n"
      "  int p = 0, f = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  initial #7 x = 0;\n"
      "  a1: assert property (@(posedge clk) 1 ##1 $past(x, 2))\n"
      "      p += $time; else f += $time;\n"
      "  initial begin #10 $arm; #30 $finish; end\n"
      "endmodule\n");

  EXPECT_EQ(IntOf("top.p"), 25);
  EXPECT_EQ(IntOf("top.f"), 35);
}

constexpr const char* kSteppedAttempts =
    "module top;\n"
    "  logic clk = 0, a = 1, b = 1, c = 1;\n"
    "  always #5 clk = ~clk;\n"
    "  a1: assert property (@(posedge clk) a ##1 b ##1 c) else begin end\n"
    "  initial begin $arm; #10 $arm; #10 $arm; #20 $finish; end\n"
    "endmodule\n";

void StepControl(int operation, uint32_t start) {
  s_vpi_time time = {vpiSimTime, 0, start, 0.0};
  vpiHandle a1 = vpi_handle_by_name(VpiText("top.a1"), nullptr);
  int result = operation == vpiAssertionEnableStep
                   ? vpi_control(operation, a1, &time, vpiAssertionClockSteps)
                   : vpi_control(operation, a1, &time);
  EXPECT_EQ(result, 1) << operation << " at " << start;
}

std::vector<std::pair<uint64_t, uint64_t>> StepsTaken() {
  std::vector<std::pair<uint64_t, uint64_t>> steps;
  for (const AssertionCall& call :
       AssertionRun::CallsOf(cbAssertionStepSuccess)) {
    steps.emplace_back(call.attempt_start, call.cb_time);
  }
  return steps;
}

TEST_F(AssertionRun, DisableStepStopsTheStepsOfTheAttemptItNames) {
  ArmInTurn({[] {
               ASSERT_NE(WatchAssertion("top.a1", cbAssertionStepSuccess),
                         nullptr);
               StepControl(vpiAssertionEnableStep, 5);
               StepControl(vpiAssertionEnableStep, 15);
             },
             [] {}, [] { StepControl(vpiAssertionDisableStep, 5); }});
  Run(kSteppedAttempts);

  EXPECT_EQ(StepsTaken(), (std::vector<std::pair<uint64_t, uint64_t>>{
                              {5, 5}, {5, 15}, {15, 15}, {15, 25}, {15, 35}}));
}

TEST_F(AssertionRun, EnableStepAfterTheAttemptBeganCallsNoStep) {
  ArmInTurn({[] {},
             [] {
               ASSERT_NE(WatchAssertion("top.a1", cbAssertionStepSuccess),
                         nullptr);
               StepControl(vpiAssertionEnableStep, 5);
               StepControl(vpiAssertionEnableStep, 25);
             }});
  Run(kSteppedAttempts);

  EXPECT_EQ(StepsTaken(),
            (std::vector<std::pair<uint64_t, uint64_t>>{{25, 25}, {25, 35}}));
}

TEST_F(AssertionRun, DISABLED_AStepControlOrKillWithoutAnAttemptTimeIsRefused) {
  ArmInTurn({[] {
    ASSERT_NE(WatchAssertion("top.a1", cbAssertionStepSuccess), nullptr);
    ASSERT_NE(WatchAssertion("top.a1", cbAssertionSuccess), nullptr);
    vpiHandle a1 = vpi_handle_by_name(VpiText("top.a1"), nullptr);
    EXPECT_EQ(vpi_control(vpiAssertionEnableStep, a1, nullptr,
                          vpiAssertionClockSteps),
              0);
    EXPECT_EQ(vpi_control(vpiAssertionDisableStep, a1, nullptr), 0);
    EXPECT_EQ(vpi_control(vpiAssertionKill, a1, nullptr), 0);
  }});
  Run(kSteppedAttempts);

  EXPECT_TRUE(StepsTaken().empty());
  std::vector<uint64_t> starts;
  for (const AssertionCall& call : CallsOf(cbAssertionSuccess)) {
    starts.push_back(call.attempt_start);
  }
  EXPECT_EQ(starts, (std::vector<uint64_t>{5, 15}));
}

TEST_F(AssertionRun, AnInferredClockStepsAtItsOwnTicks) {
  ArmInTurn({[] {
    ASSERT_NE(WatchAssertion("top.a1", cbAssertionStepSuccess), nullptr);
    ASSERT_NE(WatchAssertion("top.a2", cbAssertionStepSuccess), nullptr);
    s_vpi_time time = {vpiSimTime, 0, 5, 0.0};
    for (const char* name : {"top.a1", "top.a2"}) {
      EXPECT_EQ(vpi_control(vpiAssertionEnableStep,
                            vpi_handle_by_name(VpiText(name), nullptr), &time,
                            vpiAssertionClockSteps),
                1)
          << name;
    }
  }});
  Run("module top;\n"
      "  logic clk = 0, a = 1, b = 1, x = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  always #3 x = ~x;\n"
      "  default clocking cb @(posedge clk); endclocking\n"
      "  a1: assert property (a ##1 b) else begin end\n"
      "  always @(posedge clk) a2: assert property (a ##1 b) else begin end\n"
      "  initial begin $arm; #30 $finish; end\n"
      "endmodule\n");

  std::vector<std::pair<std::string, uint64_t>> steps;
  for (const AssertionCall& call : CallsOf(cbAssertionStepSuccess)) {
    steps.emplace_back(call.assertion, call.cb_time);
  }
  EXPECT_EQ(steps,
            (std::vector<std::pair<std::string, uint64_t>>{
                {"top.a1", 5}, {"top.a2", 5}, {"top.a1", 15}, {"top.a2", 15}}));
}

}  // namespace
