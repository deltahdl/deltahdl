#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <iterator>
#include <string>
#include <utility>
#include <vector>

#include "helpers_assertion_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

struct Step {
  int reason = 0;
  uint64_t cb_time = 0;
  uint64_t attempt_start = 0;
  int count = 0;
  int from = 0;
  int to = 0;
  bool operator==(const Step&) const = default;
};

std::vector<Step>& Steps() {
  static std::vector<Step> steps;
  return steps;
}

PLI_INT32 RecordStep(PLI_INT32 reason, p_vpi_time cb_time, vpiHandle,
                     p_vpi_attempt_info info, PLI_BYTE8*) {
  Step step;
  step.reason = reason;
  step.cb_time = cb_time != nullptr ? AssertionTicks(*cb_time) : 0;
  if (info != nullptr) {
    step.attempt_start = AssertionTicks(info->attemptStartTime);
    if (info->detail.step != nullptr) {
      step.count = info->detail.step->matched_expression_count;
      step.from = info->detail.step->stateFrom;
      step.to = info->detail.step->stateTo;
    }
  }
  Steps().push_back(step);
  return 0;
}

vpiHandle By(const char* full_name) {
  return vpi_handle_by_name(VpiText(full_name), nullptr);
}

void WatchStepsWith(int reason, uint32_t start) {
  Steps().clear();
  ASSERT_NE(
      vpi_register_assertion_cb(By("top.a1"), reason, &RecordStep, nullptr),
      nullptr);
  s_vpi_time time = {vpiSimTime, 0, start, 0.0};
  EXPECT_EQ(vpi_control(vpiAssertionEnableStep, By("top.a1"), &time,
                        vpiAssertionClockSteps),
            1);
}

std::string StepDesign(const char* property) {
  std::string src =
      "module top; logic clk = 0, a = 1, b = 1, d = 0;\n"
      "  always #5 clk = ~clk;\n"
      "  a1: assert property (@(posedge clk) ";
  src += property;
  src +=
      ") else begin end\n"
      "  initial begin $arm; #40 $finish; end\n"
      "endmodule\n";
  return src;
}

TEST_F(AssertionRun, EachStepCarriesTheTimeOfTheStepAndTheAttemptsStart) {
  ArmInTurn({[] { WatchStepsWith(cbAssertionStepSuccess, 15); }});
  Run(StepDesign("a ##1 b ##1 d"));
  ASSERT_EQ(Steps().size(), 3u);
  EXPECT_EQ(Steps()[0].reason, cbAssertionStepSuccess);
  EXPECT_EQ(Steps()[1].reason, cbAssertionStepSuccess);
  EXPECT_EQ(Steps()[2].reason, cbAssertionStepFailure);
  for (size_t i = 0; i < Steps().size(); ++i) {
    EXPECT_EQ(Steps()[i].cb_time, 15 + (10 * i)) << i;
    EXPECT_EQ(Steps()[i].attempt_start, 15u) << i;
  }
}

TEST_F(AssertionRun, AStepFailureCallbackIsAlsoCalledForASuccessfulStep) {
  ArmInTurn({[] { WatchStepsWith(cbAssertionStepFailure, 15); }});
  Run(StepDesign("a ##1 b ##1 d"));
  std::vector<std::pair<int, uint64_t>> got;
  for (const Step& step : Steps()) got.emplace_back(step.reason, step.cb_time);
  EXPECT_EQ(got, (std::vector<std::pair<int, uint64_t>>{
                     {cbAssertionStepSuccess, 15},
                     {cbAssertionStepSuccess, 25},
                     {cbAssertionStepFailure, 35}}));
}

TEST_F(AssertionRun, AnUnconditionalStepMatchesNoExpression) {
  ArmInTurn({[] { WatchStepsWith(cbAssertionStepSuccess, 5); }});
  Run(StepDesign("a ##2 b"));
  ASSERT_EQ(Steps().size(), 3u);
  EXPECT_EQ(Steps()[0].count, 1);
  EXPECT_EQ(Steps()[1].count, 0);
  EXPECT_EQ(Steps()[1].cb_time, 15u);
  EXPECT_NE(Steps()[1].from, Steps()[1].to);
  EXPECT_EQ(Steps()[1].from, Steps()[0].to);
  EXPECT_EQ(Steps()[1].to, Steps()[2].from);
  EXPECT_EQ(Steps()[2].to, 1);
}

void Control(int operation) {
  EXPECT_EQ(vpi_control(operation, By("top.af")), 1) << operation;
}

constexpr const char* kOneAssertion =
    "module top; logic clk = 0, a = 1;\n"
    "  always #1 clk = ~clk;\n"
    "  af: assert property (@(posedge clk) a);\n"
    "  initial begin $arm; #4 $arm; #2 $arm; #2 $arm; #2 $finish; end\n"
    "endmodule\n";

TEST_F(AssertionRun, AControlCallbackCarriesTheTimeOfTheControl) {
  ArmInTurn({[] {
               for (int reason : {cbAssertionDisable, cbAssertionEnable,
                                  cbAssertionKill, cbAssertionReset}) {
                 ASSERT_NE(WatchAssertion("top.af", reason), nullptr);
               }
             },
             [] {
               Control(vpiAssertionDisable);
               Control(vpiAssertionEnable);
             },
             [] { Control(vpiAssertionKill); },
             [] { Control(vpiAssertionReset); }});
  Run(kOneAssertion);
  std::vector<std::pair<int, uint64_t>> got;
  for (const AssertionCall& call : AssertionCalls()) {
    got.emplace_back(call.reason, call.cb_time);
  }
  EXPECT_EQ(got,
            (std::vector<std::pair<int, uint64_t>>{{cbAssertionDisable, 4},
                                                   {cbAssertionEnable, 4},
                                                   {cbAssertionKill, 6},
                                                   {cbAssertionReset, 8}}));
}

constexpr std::pair<int, int> kAssertionControls[] = {
    {vpiAssertionLock, cbAssertionLock},
    {vpiAssertionUnlock, cbAssertionUnlock},
    {vpiAssertionDisablePassAction, cbAssertionDisablePassAction},
    {vpiAssertionEnablePassAction, cbAssertionEnablePassAction},
    {vpiAssertionDisableFailAction, cbAssertionDisableFailAction},
    {vpiAssertionEnableFailAction, cbAssertionEnableFailAction},
    {vpiAssertionDisableVacuousAction, cbAssertionDisableVacuousAction},
    {vpiAssertionEnableNonvacuousAction, cbAssertionEnableNonvacuousAction},
    {vpiAssertionReset, cbAssertionReset}};

void WatchEachControlReason() {
  for (const auto& [operation, reason] : kAssertionControls) {
    ASSERT_NE(WatchAssertion("top.af", reason), nullptr) << reason;
  }
}

std::vector<int> ExpectedControlReasons() {
  std::vector<int> reasons;
  reasons.reserve(std::size(kAssertionControls));
  for (const auto& [operation, reason] : kAssertionControls) {
    reasons.push_back(reason);
  }
  return reasons;
}

std::vector<int> ReasonsWithoutInfo() {
  std::vector<int> reasons;
  for (const AssertionCall& call : AssertionCalls()) {
    EXPECT_FALSE(call.has_info) << call.reason;
    EXPECT_EQ(call.assertion, "top.af");
    reasons.push_back(call.reason);
  }
  return reasons;
}

TEST_F(AssertionRun, EachAssertionControlCallsItsCallbackWithNoAttemptInfo) {
  ArmInTurn({[] {
    WatchEachControlReason();
    for (const auto& [operation, reason] : kAssertionControls) {
      Control(operation);
    }
  }});
  Run(kOneAssertion);
  EXPECT_EQ(ReasonsWithoutInfo(), ExpectedControlReasons());
}

std::string ControlTaskCall(const char* task, const char* control, bool named) {
  std::string call = task;
  if (named) {
    call += "(";
    if (*control != '\0') {
      call += control;
      call += ", 15, 7, ";
    }
    call += "0, af)";
  } else if (*control != '\0') {
    call += "(";
    call += control;
    call += ")";
  }
  call += ";";
  return call;
}

std::string ControlTaskDesign(bool named) {
  std::string src =
      "module top; logic clk = 0, a = 1;\n"
      "  always #1 clk = ~clk;\n"
      "  af: assert property (@(posedge clk) a);\n"
      "  initial begin $arm;\n";
  for (const auto& [task, control] :
       {std::pair{"$assertcontrol", "1"}, std::pair{"$assertcontrol", "2"},
        std::pair{"$assertpassoff", ""}, std::pair{"$assertpasson", ""},
        std::pair{"$assertfailoff", ""}, std::pair{"$assertfailon", ""},
        std::pair{"$assertvacuousoff", ""},
        std::pair{"$assertnonvacuouson", ""}}) {
    src += "    ";
    src += ControlTaskCall(task, control, named);
    src += "\n";
  }
  src +=
      "    #4 $finish;\n"
      "  end\n"
      "endmodule\n";
  return src;
}

std::vector<int> ControlTaskReasons() {
  std::vector<int> reasons = ExpectedControlReasons();
  reasons.pop_back();
  return reasons;
}

TEST_F(AssertionRun, EachControlTaskNamingTheAssertionCallsItsCallback) {
  ArmInTurn({[] { WatchEachControlReason(); }});
  Run(ControlTaskDesign(true));
  EXPECT_EQ(ReasonsWithoutInfo(), ControlTaskReasons());
}

TEST_F(AssertionRun, DISABLED_EachControlTaskOfTheWholeDesignCallsItsCallback) {
  ArmInTurn({[] { WatchEachControlReason(); }});
  Run(ControlTaskDesign(false));
  EXPECT_EQ(ReasonsWithoutInfo(), ControlTaskReasons());
}

TEST_F(AssertionRun, AReasonThatIsNoAssertionCallbackPlacesNothing) {
  ArmInTurn({[this] {
    EXPECT_EQ(vpi_register_assertion_cb(By("top.af"), vpiAssertionSysOff,
                                        &RecordAssertionCall, nullptr),
              nullptr);
    EXPECT_EQ(api_.PlacedCallbackCount(), 0u);
  }});
  Run(kOneAssertion);
  EXPECT_TRUE(AssertionCalls().empty());
}

constexpr const char* kInstances =
    "module top; logic clk = 0, a = 1, b = 1, c = 1;\n"
    "  always #1 clk = ~clk;\n"
    "  sequence s; @(posedge clk) a ##1 b; endsequence\n"
    "  property p; @(posedge clk) c; endproperty\n"
    "  c1: cover sequence (s);\n"
    "  a1: assert property (p) else begin end\n"
    "  initial begin $arm; #4 b = 0; c = 0; #4 $finish; end\n"
    "endmodule\n";

vpiHandle InstanceOf(int type) {
  vpiHandle it = vpi_iterate(vpiAssertion, By("top"));
  while (vpiHandle obj = it == nullptr ? nullptr : vpi_scan(it)) {
    if (vpi_get(vpiType, obj) == type) return obj;
  }
  return nullptr;
}

void WatchInstance(int type, int reason) {
  vpiHandle inst = InstanceOf(type);
  ASSERT_NE(inst, nullptr) << type;
  ASSERT_NE(
      vpi_register_assertion_cb(inst, reason, &RecordAssertionCall, nullptr),
      nullptr)
      << type << " " << reason;
}

using Timings = std::vector<std::pair<uint64_t, uint64_t>>;

Timings TimingsOf(int reason) {
  Timings timings;
  for (const AssertionCall& call : AssertionRun::CallsOf(reason)) {
    timings.emplace_back(call.cb_time, call.attempt_start);
  }
  return timings;
}

void WatchEachInstance(int type) {
  for (int reason :
       {cbAssertionStart, cbAssertionSuccess, cbAssertionFailure}) {
    WatchInstance(type, reason);
  }
}

TEST_F(AssertionRun,
       DISABLED_APropertyInstancesStartSuccessAndFailureAreCalled) {
  ArmInTurn({[] { WatchEachInstance(vpiPropertyInst); }});
  Run(kInstances);
  EXPECT_EQ(TimingsOf(cbAssertionStart),
            (Timings{{1, 1}, {3, 3}, {5, 5}, {7, 7}}));
  EXPECT_EQ(TimingsOf(cbAssertionSuccess), (Timings{{1, 1}, {3, 3}}));
  EXPECT_EQ(TimingsOf(cbAssertionFailure), (Timings{{5, 5}, {7, 7}}));
}

TEST_F(AssertionRun, DISABLED_ASequenceInstancesStartMatchAndFailureAreCalled) {
  ArmInTurn({[] { WatchEachInstance(vpiSequenceInst); }});
  Run(kInstances);
  EXPECT_EQ(TimingsOf(cbAssertionStart),
            (Timings{{1, 1}, {3, 3}, {5, 5}, {7, 7}}));
  EXPECT_EQ(TimingsOf(cbAssertionSuccess), (Timings{{3, 1}}));
  EXPECT_EQ(TimingsOf(cbAssertionFailure), (Timings{{5, 3}, {7, 5}}));
}

TEST_F(AssertionRun, AnInstanceNoVerificationStatementHoldsNeverStarts) {
  ArmInTurn({[] {
    vpiHandle it = vpi_iterate(vpiPropertyDecl, By("top"));
    vpiHandle q = nullptr;
    while (vpiHandle obj = it == nullptr ? nullptr : vpi_scan(it)) {
      const char* name = vpi_get_str(vpiName, obj);
      if (name != nullptr && std::string(name) == "q") q = obj;
    }
    ASSERT_NE(q, nullptr);
    vpiHandle inst =
        vpi_handle(vpiPropertyExpr, vpi_handle(vpiPropertySpec, q));
    ASSERT_NE(inst, nullptr);
    ASSERT_EQ(vpi_get(vpiType, inst), vpiSequenceInst);
    ASSERT_NE(vpi_register_assertion_cb(inst, cbAssertionStart,
                                        &RecordAssertionCall, nullptr),
              nullptr);
  }});
  Run("module top; logic clk = 0, a = 1;\n"
      "  always #1 clk = ~clk;\n"
      "  sequence s; @(posedge clk) a; endsequence\n"
      "  property q; s; endproperty\n"
      "  initial begin $arm; #4 $finish; end\n"
      "endmodule\n");
  EXPECT_TRUE(AssertionCalls().empty());
}

TEST_F(AssertionRun, AnInstanceTakesOnlyStartSuccessAndFailureCallbacks) {
  ArmInTurn({[this] {
    for (int type : {vpiSequenceInst, vpiPropertyInst}) {
      vpiHandle inst = InstanceOf(type);
      ASSERT_NE(inst, nullptr) << type;
      for (int reason :
           {cbAssertionVacuousSuccess, cbAssertionDisable, cbAssertionReset,
            cbAssertionKill, cbAssertionStepSuccess, cbAssertionLock}) {
        EXPECT_EQ(vpi_register_assertion_cb(inst, reason, &RecordAssertionCall,
                                            nullptr),
                  nullptr)
            << type << " " << reason;
      }
      EXPECT_EQ(api_.PlacedCallbackCount(), 0u);
    }
    for (int type : {vpiSequenceInst, vpiPropertyInst}) {
      WatchEachInstance(type);
    }
    EXPECT_EQ(api_.PlacedCallbackCount(), 6u);
    for (const auto& [operation, reason] : kAssertionControls) {
      vpi_control(operation, By("top.a1"));
    }
  }});
  Run(kInstances);
  for (const AssertionCall& call : AssertionCalls()) {
    EXPECT_TRUE(call.reason == cbAssertionStart ||
                call.reason == cbAssertionSuccess ||
                call.reason == cbAssertionFailure)
        << call.reason;
  }
}

}  // namespace
}  // namespace delta
