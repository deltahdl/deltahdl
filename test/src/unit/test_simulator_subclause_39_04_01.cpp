#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <iterator>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_assertion_run.h"
#include "simulator/assertion_api.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

constexpr int kSysReasons[] = {cbAssertionSysInitialized,
                               cbAssertionSysLock,
                               cbAssertionSysUnlock,
                               cbAssertionSysOn,
                               cbAssertionSysOff,
                               cbAssertionSysKill,
                               cbAssertionSysEnd,
                               cbAssertionSysReset,
                               cbAssertionSysEnablePassAction,
                               cbAssertionSysEnableFailAction,
                               cbAssertionSysDisablePassAction,
                               cbAssertionSysDisableFailAction,
                               cbAssertionSysEnableNonvacuousAction,
                               cbAssertionSysDisableVacuousAction};

TEST(AssertionSysCallback, ReasonConstantsDefinedDistinctAndRecognized) {
  for (size_t i = 0; i < std::size(kSysReasons); ++i) {
    EXPECT_TRUE(AssertionApi::IsAssertionSysCallbackReason(kSysReasons[i]));
    for (size_t j = i + 1; j < std::size(kSysReasons); ++j) {
      EXPECT_NE(kSysReasons[i], kSysReasons[j]);
    }
  }
}

TEST(AssertionSysCallback, NonSystemReasonsNotRecognized) {
  EXPECT_FALSE(AssertionApi::IsAssertionSysCallbackReason(cbAssertionStart));
  EXPECT_FALSE(AssertionApi::IsAssertionSysCallbackReason(cbAssertionSuccess));
  EXPECT_FALSE(AssertionApi::IsAssertionSysCallbackReason(cbAssertionDisable));
  EXPECT_FALSE(
      AssertionApi::IsAssertionSysCallbackReason(cbAssertionDisablePassAction));
  EXPECT_FALSE(AssertionApi::IsAssertionSysCallbackReason(cbEndOfSimulation));
  EXPECT_FALSE(AssertionApi::IsAssertionSysCallbackReason(vpiAssertionSysOff));
}

class AssertionSysCallbackPlacement : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

namespace {
int g_seen_reason = 0;
void* g_seen_user_data = nullptr;
int RecordSysCb(s_cb_data* data) {
  if (data) {
    g_seen_reason = data->reason;
    g_seen_user_data = data->user_data;
  }
  return 0;
}
}  // namespace

TEST_F(AssertionSysCallbackPlacement, RegisterByEverySysReasonReturnsHandle) {
  for (int reason : kSysReasons) {
    ASSERT_TRUE(AssertionApi::IsAssertionSysCallbackReason(reason));
    s_cb_data cb = {};
    cb.reason = reason;
    cb.cb_rtn = &RecordSysCb;
    vpiHandle h = vpi_register_cb(&cb);
    EXPECT_NE(h, nullptr);
    EXPECT_EQ(vpi_ctx_.RegisteredCallbacks().back().reason, reason);
  }
}

TEST_F(AssertionSysCallbackPlacement, DeliveryCarriesReasonAndUserData) {
  int payload = 99;
  s_cb_data cb = {};
  cb.reason = cbAssertionSysOn;
  cb.cb_rtn = &RecordSysCb;
  cb.user_data = reinterpret_cast<PLI_BYTE8*>(&payload);
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);

  g_seen_reason = 0;
  g_seen_user_data = nullptr;
  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbAssertionSysOn), 1);
  EXPECT_EQ(g_seen_reason, cbAssertionSysOn);
  EXPECT_EQ(g_seen_user_data, &payload);
}

TEST_F(AssertionSysCallbackPlacement,
       DeliveryCarriesNullUserDataWhenNoneGiven) {
  s_cb_data cb = {};
  cb.reason = cbAssertionSysInitialized;
  cb.cb_rtn = &RecordSysCb;
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);

  int sentinel = 0;
  g_seen_reason = 0;
  g_seen_user_data = &sentinel;
  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbAssertionSysInitialized), 1);
  EXPECT_EQ(g_seen_reason, cbAssertionSysInitialized);
  EXPECT_EQ(g_seen_user_data, nullptr);
}

TEST_F(AssertionSysCallbackPlacement, DeliveryIsSelectiveByReason) {
  s_cb_data cb = {};
  cb.reason = cbAssertionSysEnd;
  cb.cb_rtn = &RecordSysCb;
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);

  g_seen_reason = 0;
  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbAssertionSysReset), 0);
  EXPECT_EQ(g_seen_reason, 0);

  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbAssertionSysEnd), 1);
  EXPECT_EQ(g_seen_reason, cbAssertionSysEnd);
}

constexpr int kDesignRan = -1;

std::vector<int> RecordedReasons() {
  std::vector<int> reasons;
  for (const AssertionCall& call : AssertionCalls()) {
    reasons.push_back(call.reason);
  }
  return reasons;
}

TEST_F(AssertionRun, TheAssertionSystemStartsAndEndsWithTheRun) {
  for (int reason :
       {cbAssertionSysInitialized, cbAssertionSysOn, cbAssertionSysEnd}) {
    ASSERT_NE(WatchAssertionSystem(reason), nullptr);
  }
  AssertionArmer() = [] {
    AssertionCall ran;
    ran.reason = kDesignRan;
    AssertionCalls().push_back(ran);
  };
  Run("module top;\n"
      "  initial $arm;\n"
      "  final $arm;\n"
      "endmodule\n");
  f_.scheduler.EndSimulation();

  EXPECT_EQ(RecordedReasons(),
            (std::vector<int>{cbAssertionSysInitialized, cbAssertionSysOn,
                              kDesignRan, kDesignRan, cbAssertionSysEnd}));
}

TEST_F(AssertionRun, AnAssertionSystemTurnedOffBeforeTheRunDoesNotStart) {
  for (int reason : {cbAssertionSysInitialized, cbAssertionSysOn}) {
    ASSERT_NE(WatchAssertionSystem(reason), nullptr);
  }
  ASSERT_EQ(vpi_control(vpiAssertionSysOff, static_cast<vpiHandle>(nullptr)),
            1);
  Run("module top;\n"
      "  initial $noop;\n"
      "endmodule\n");

  EXPECT_EQ(RecordedReasons(), (std::vector<int>{cbAssertionSysInitialized}));
}

TEST_F(AssertionRun, AnAssertionSystemEndedDuringTheRunEndsOnce) {
  ASSERT_NE(WatchAssertionSystem(cbAssertionSysEnd), nullptr);
  AssertionArmer() = [] {
    vpi_control(vpiAssertionSysEnd, static_cast<vpiHandle>(nullptr));
  };
  Run("module top;\n"
      "  initial #5 $arm;\n"
      "endmodule\n");
  f_.scheduler.EndSimulation();

  ASSERT_EQ(CallsOf(cbAssertionSysEnd).size(), 1u);
  EXPECT_EQ(CallsOf(cbAssertionSysEnd)[0].now, 5u);
}

void SysControl(int operation) {
  vpi_control(operation, static_cast<vpiHandle>(nullptr));
}

std::vector<uint64_t> TimesOf(int reason, const char* assertion) {
  std::vector<uint64_t> times;
  for (const AssertionCall& call : AssertionRun::CallsOf(reason)) {
    if (call.assertion == assertion) times.push_back(call.now);
  }
  return times;
}

constexpr const char* kTwoWindows =
    "module top; logic clk = 0, a = 0;\n"
    "  always #1 clk = ~clk;\n"
    "  af: assert property (@(posedge clk) a);\n"
    "  ap: assert property (@(posedge clk) !a);\n"
    "  initial begin $arm; #4 $arm; #4 $arm; #4 $arm; #4 $arm; #4 $finish; "
    "end\n"
    "endmodule\n";

void WatchBothAssertions() {
  WatchAssertion("top.af", cbAssertionStart);
  WatchAssertion("top.af", cbAssertionFailure);
  WatchAssertion("top.ap", cbAssertionSuccess);
}

void ExpectAttemptsOnlyOutsideTheWindows() {
  const std::vector<uint64_t> kOutside = {1, 3, 9, 11, 17, 19};
  EXPECT_EQ(TimesOf(cbAssertionStart, "top.af"), kOutside);
  EXPECT_EQ(TimesOf(cbAssertionFailure, "top.af"), kOutside);
  EXPECT_EQ(TimesOf(cbAssertionSuccess, "top.ap"), kOutside);
}

std::vector<uint64_t> SystemTimesOf(int reason) {
  std::vector<uint64_t> times;
  for (const AssertionCall& call : AssertionRun::CallsOf(reason)) {
    times.push_back(call.now);
  }
  return times;
}

TEST_F(AssertionRun, EachKillCallsItsCallbackAndStopsAttemptsUntilResumed) {
  ArmInTurn({[] {
               WatchBothAssertions();
               WatchAssertionSystem(cbAssertionSysKill);
             },
             [] { SysControl(vpiAssertionSysKill); },
             [] { SysControl(vpiAssertionSysOn); },
             [] { SysControl(vpiAssertionSysKill); },
             [] { SysControl(vpiAssertionSysOn); }});
  Run(kTwoWindows);
  EXPECT_EQ(SystemTimesOf(cbAssertionSysKill), (std::vector<uint64_t>{4, 12}));
  ExpectAttemptsOnlyOutsideTheWindows();
}

TEST_F(AssertionRun, EachOffWindowStartsNoAttemptAndCallsNoCallback) {
  ArmInTurn({[] {
               WatchBothAssertions();
               WatchAssertionSystem(cbAssertionSysOff);
             },
             [] { SysControl(vpiAssertionSysOff); },
             [] { SysControl(vpiAssertionSysOn); },
             [] { SysControl(vpiAssertionSysOff); },
             [] { SysControl(vpiAssertionSysOn); }});
  Run(kTwoWindows);
  EXPECT_EQ(SystemTimesOf(cbAssertionSysOff), (std::vector<uint64_t>{4, 12}));
  ExpectAttemptsOnlyOutsideTheWindows();
}

std::vector<uint64_t> AttemptStartsOf(int reason, const char* assertion) {
  std::vector<uint64_t> starts;
  for (const AssertionCall& call : AssertionRun::CallsOf(reason)) {
    if (call.assertion == assertion) starts.push_back(call.attempt_start);
  }
  return starts;
}

TEST_F(AssertionRun, AnAttemptInFlightWhenTheSystemGoesOffStillCallsBack) {
  ArmInTurn({[] { WatchAssertion("top.al", cbAssertionFailure); },
             [] { SysControl(vpiAssertionSysOff); }});
  Run("module top; logic clk = 0, a = 0;\n"
      "  always #1 clk = ~clk;\n"
      "  al: assert property (@(posedge clk) 1 ##2 a);\n"
      "  initial begin $arm; #4 $arm; #8 $finish; end\n"
      "endmodule\n");
  EXPECT_EQ(TimesOf(cbAssertionFailure, "top.al"),
            (std::vector<uint64_t>{5, 7}));
  EXPECT_EQ(AttemptStartsOf(cbAssertionFailure, "top.al"),
            (std::vector<uint64_t>{1, 3}));
}

TEST_F(AssertionRun, NoAttemptStartsOrActsAfterTheSystemEnds) {
  ArmInTurn({[] { WatchAssertion("top.af", cbAssertionStart); },
             [] { SysControl(vpiAssertionSysEnd); }});
  Run("module top; logic clk = 0, a = 0; int n = 0;\n"
      "  always #1 clk = ~clk;\n"
      "  af: assert property (@(posedge clk) a) else n++;\n"
      "  initial begin $arm; #4 $arm; #8 $finish; end\n"
      "endmodule\n");
  EXPECT_EQ(TimesOf(cbAssertionStart, "top.af"), (std::vector<uint64_t>{1, 3}));
  EXPECT_EQ(IntOf("top.n"), 2);
}

TEST_F(AssertionRun, DISABLED_AnAttemptInFlightAtTheEndReachesItsVerdictFirst) {
  ArmInTurn({[] {
    for (int reason :
         {cbAssertionSuccess, cbAssertionVacuousSuccess, cbAssertionFailure}) {
      WatchAssertion("top.al", reason);
    }
    WatchAssertionSystem(cbAssertionSysEnd);
  }});
  Run("module top; logic clk = 0, a = 0;\n"
      "  always #1 clk = ~clk;\n"
      "  al: assert property (@(posedge clk) 1 ##2 a);\n"
      "  initial begin $arm; #6 $finish; end\n"
      "endmodule\n");
  f_.scheduler.EndSimulation();
  const std::vector<AssertionCall>& calls = AssertionCalls();
  ASSERT_FALSE(calls.empty());
  EXPECT_EQ(calls.back().reason, cbAssertionSysEnd);
  std::vector<uint64_t> verdicts;
  for (const AssertionCall& call : calls) {
    if (call.assertion == "top.al") verdicts.push_back(call.attempt_start);
  }
  EXPECT_EQ(verdicts, (std::vector<uint64_t>{1, 3, 5}));
}

TEST_F(AssertionRun, AControlAfterTheSystemEndsCallsNoSystemCallback) {
  ArmInTurn({[] {
               WatchAssertionSystem(cbAssertionSysOn);
               WatchAssertionSystem(cbAssertionSysOff);
             },
             [] { SysControl(vpiAssertionSysEnd); },
             [] {
               SysControl(vpiAssertionSysOff);
               SysControl(vpiAssertionSysOn);
             }});
  Run("module top;\n"
      "  initial begin $arm; #4 $arm; #4 $arm; end\n"
      "endmodule\n");
  f_.scheduler.EndSimulation();
  SysControl(vpiAssertionSysOff);
  SysControl(vpiAssertionSysOn);
  EXPECT_TRUE(CallsOf(cbAssertionSysOn).empty());
  EXPECT_TRUE(CallsOf(cbAssertionSysOff).empty());
}

PLI_INT32 DisableTheAssertionWhileInitializing(p_cb_data) {
  vpi_control(vpiAssertionDisable,
              vpi_handle_by_name(VpiText("top.af"), nullptr));
  return 0;
}

TEST_F(AssertionRun,
       DISABLED_AnAssertionActionInsideTheInitializedCallbackHasNoEffect) {
  s_cb_data data = {};
  data.reason = cbAssertionSysInitialized;
  data.cb_rtn = &DisableTheAssertionWhileInitializing;
  ASSERT_NE(vpi_register_cb(&data), nullptr);
  ArmInTurn({[] { WatchAssertion("top.af", cbAssertionFailure); }});
  Run("module top; logic clk = 0, a = 0;\n"
      "  always #1 clk = ~clk;\n"
      "  af: assert property (@(posedge clk) a);\n"
      "  initial begin $arm; #4 $finish; end\n"
      "endmodule\n");
  EXPECT_EQ(TimesOf(cbAssertionFailure, "top.af"),
            (std::vector<uint64_t>{1, 3}));
}

constexpr std::pair<int, int> kSysControls[] = {
    {vpiAssertionSysLock, cbAssertionSysLock},
    {vpiAssertionSysUnlock, cbAssertionSysUnlock},
    {vpiAssertionSysDisablePassAction, cbAssertionSysDisablePassAction},
    {vpiAssertionSysEnablePassAction, cbAssertionSysEnablePassAction},
    {vpiAssertionSysDisableFailAction, cbAssertionSysDisableFailAction},
    {vpiAssertionSysEnableFailAction, cbAssertionSysEnableFailAction},
    {vpiAssertionSysDisableVacuousAction, cbAssertionSysDisableVacuousAction},
    {vpiAssertionSysEnableNonvacuousAction,
     cbAssertionSysEnableNonvacuousAction}};

TEST_F(AssertionRun, EachSystemUnlockAndActionControlCallsItsCallback) {
  ArmInTurn({[] {
    for (const auto& [operation, reason] : kSysControls) {
      WatchAssertionSystem(reason);
    }
    for (const auto& [operation, reason] : kSysControls) SysControl(operation);
  }});
  Run("module top;\n"
      "  initial $arm;\n"
      "endmodule\n");
  std::vector<int> expected;
  expected.reserve(std::size(kSysControls));
  for (const auto& [operation, reason] : kSysControls) {
    expected.push_back(reason);
  }
  EXPECT_EQ(RecordedReasons(), expected);
}

}  // namespace
}  // namespace delta
