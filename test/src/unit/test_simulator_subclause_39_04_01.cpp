#include <gtest/gtest.h>

#include <iterator>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/dpi_runtime.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// The fourteen reasons §39.4.1 lists for placing an assertion system callback.
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

// §39.4.1: each value listed for the reason element of s_cb_data is a defined,
// distinct assertion-system callback reason that production code recognizes as
// such.
TEST(AssertionSysCallback, ReasonConstantsDefinedDistinctAndRecognized) {
  for (size_t i = 0; i < std::size(kSysReasons); ++i) {
    EXPECT_TRUE(AssertionApi::IsAssertionSysCallbackReason(kSysReasons[i]));
    for (size_t j = i + 1; j < std::size(kSysReasons); ++j) {
      EXPECT_NE(kSysReasons[i], kSysReasons[j]);
    }
  }
}

// §39.4.1: the assertion-system callback reasons are distinct from the
// per-assertion callback reasons of §39.4.2 and from unrelated VPI callback
// reasons; none of those name an assertion system callback.
TEST(AssertionSysCallback, NonSystemReasonsNotRecognized) {
  // Per-assertion callback reasons (§39.4.2) are not system reasons.
  EXPECT_FALSE(AssertionApi::IsAssertionSysCallbackReason(cbAssertionStart));
  EXPECT_FALSE(AssertionApi::IsAssertionSysCallbackReason(cbAssertionSuccess));
  EXPECT_FALSE(AssertionApi::IsAssertionSysCallbackReason(cbAssertionDisable));
  EXPECT_FALSE(
      AssertionApi::IsAssertionSysCallbackReason(cbAssertionDisablePassAction));
  // An ordinary simulation callback reason is not an assertion system reason.
  EXPECT_FALSE(AssertionApi::IsAssertionSysCallbackReason(cbEndOfSimulation));
  // A vpi_control() system-control constant is not a callback reason.
  EXPECT_FALSE(AssertionApi::IsAssertionSysCallbackReason(vpiAssertionSysOff));
}

// §38.36 provides the generic vpi_register_cb()/s_cb_data machinery; this
// fixture exercises it with the §39.4.1 assertion-system reasons.
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
int RecordSysCb(VpiCbData* data) {
  if (data) {
    g_seen_reason = data->reason;
    g_seen_user_data = data->user_data;
  }
  return 0;
}
}  // namespace

// §39.4.1: an assertion system callback is placed with vpi_register_cb(),
// setting cb_rtn to the routine and the reason element to one of the listed
// assertion-system reasons. The placement returns a callback handle.
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

// §39.4.1: the routine invoked follows the normal VPI callback prototype and is
// passed an s_cb_data containing the callback reason and any user data provided
// to the vpi_register_cb() call.
TEST_F(AssertionSysCallbackPlacement, DeliveryCarriesReasonAndUserData) {
  int payload = 99;
  s_cb_data cb = {};
  cb.reason = cbAssertionSysOn;
  cb.cb_rtn = &RecordSysCb;
  cb.user_data = &payload;
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);

  g_seen_reason = 0;
  g_seen_user_data = nullptr;
  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbAssertionSysOn), 1);
  EXPECT_EQ(g_seen_reason, cbAssertionSysOn);
  EXPECT_EQ(g_seen_user_data, &payload);
}

// §39.4.1: "any user data" spans the case where none is supplied. A system
// callback registered without a user_data pointer is still delivered, and the
// s_cb_data its routine receives carries a null user_data beside the reason.
TEST_F(AssertionSysCallbackPlacement,
       DeliveryCarriesNullUserDataWhenNoneGiven) {
  s_cb_data cb = {};
  cb.reason = cbAssertionSysInitialized;
  cb.cb_rtn = &RecordSysCb;
  // user_data is left at its default null: the registration provides none.
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);

  // Seed the observation with a sentinel so a delivered null is distinguishable
  // from the routine never having run.
  int sentinel = 0;
  g_seen_reason = 0;
  g_seen_user_data = &sentinel;
  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbAssertionSysInitialized), 1);
  EXPECT_EQ(g_seen_reason, cbAssertionSysInitialized);
  EXPECT_EQ(g_seen_user_data, nullptr);
}

// §39.4.1: because each assertion-system reason is distinct, a callback placed
// for one system reason is delivered only for that reason. Dispatching a
// different system reason does not invoke it; dispatching its own reason does.
TEST_F(AssertionSysCallbackPlacement, DeliveryIsSelectiveByReason) {
  s_cb_data cb = {};
  cb.reason = cbAssertionSysEnd;
  cb.cb_rtn = &RecordSysCb;
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);

  // A different assertion-system reason matches no registered callback.
  g_seen_reason = 0;
  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbAssertionSysReset), 0);
  EXPECT_EQ(g_seen_reason, 0);

  // The reason it was placed for delivers exactly once.
  EXPECT_EQ(vpi_ctx_.DispatchCallbacks(cbAssertionSysEnd), 1);
  EXPECT_EQ(g_seen_reason, cbAssertionSysEnd);
}

}  // namespace
}  // namespace delta
