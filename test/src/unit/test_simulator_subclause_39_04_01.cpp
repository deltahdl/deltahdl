#include <gtest/gtest.h>

#include <cstddef>
#include <iterator>
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

}  // namespace
}  // namespace delta
