#include <gtest/gtest.h>

#include <iterator>
#include <set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §38.36.3: the simulator executes a callback by invoking its cb_rtn and
// passing a pointer to the s_cb_data structure, whose reason field holds the
// reason for the callback. This recorder lets a test observe that contract
// being applied.
int g_invocations = 0;
int g_seen_reason = 0;
void* g_seen_user_data = nullptr;
VpiHandle g_seen_obj = nullptr;
std::vector<int> g_sequence;

int RecordingCb(VpiCbData* data) {
  ++g_invocations;
  if (data) {
    g_seen_reason = data->reason;
    g_seen_user_data = data->user_data;
    g_seen_obj = data->obj;
    g_sequence.push_back(data->reason);
  }
  return 0;
}

// §38.36.3 action callbacks: reasons that every VPI-compliant tool provides.
const int kActionReasons[] = {
    cbEndOfCompile, cbStartOfSimulation, cbEndOfSimulation, cbError,
    cbPLIError,     cbTchkViolation,     cbSignal,
};

// §38.36.3 feature callbacks: optional, tool-specific reasons.
const int kFeatureReasons[] = {
    cbStartOfSave,      cbEndOfSave,       cbStartOfRestart,
    cbEndOfRestart,     cbStartOfReset,    cbEndOfReset,
    cbEnterInteractive, cbExitInteractive, cbInteractiveScopeChange,
    cbUnresolvedSystf,
};

class VpiActionFeatureCallbacks : public ::testing::Test {
 protected:
  void SetUp() override {
    g_invocations = 0;
    g_seen_reason = 0;
    g_seen_user_data = nullptr;
    g_seen_obj = nullptr;
    g_sequence.clear();
    SetGlobalVpiContext(&vpi_ctx_);
  }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  vpiHandle Register(int reason) {
    s_cb_data cb = {};
    cb.reason = reason;
    cb.cb_rtn = &RecordingCb;
    return vpi_register_cb(&cb);
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

// §38.36.3: the listed action-related callbacks shall be defined. Registering
// each one yields a callback handle and records the reason that was requested.
TEST_F(VpiActionFeatureCallbacks, ActionReasonsAreDefinedAndRegister) {
  for (int reason : kActionReasons) {
    s_cb_data cb = {};
    cb.reason = reason;
    cb.cb_rtn = &RecordingCb;
    vpiHandle h = vpi_register_cb(&cb);
    EXPECT_NE(h, nullptr) << "reason=" << reason;
    EXPECT_EQ(vpi_ctx_.RegisteredCallbacks().back().reason, reason);
  }
}

// §38.36.3: the feature-related callback reasons are likewise registrable
// through the same vpi_register_cb() mechanism.
TEST_F(VpiActionFeatureCallbacks, FeatureReasonsAreDefinedAndRegister) {
  for (int reason : kFeatureReasons) {
    s_cb_data cb = {};
    cb.reason = reason;
    cb.cb_rtn = &RecordingCb;
    vpiHandle h = vpi_register_cb(&cb);
    EXPECT_NE(h, nullptr) << "reason=" << reason;
    EXPECT_EQ(vpi_ctx_.RegisteredCallbacks().back().reason, reason);
  }
}

// §38.36.3: every action and feature reason denotes a distinct callback reason.
TEST_F(VpiActionFeatureCallbacks, ReasonCodesAreDistinct) {
  std::set<int> seen;
  for (int reason : kActionReasons) seen.insert(reason);
  for (int reason : kFeatureReasons) seen.insert(reason);
  EXPECT_EQ(seen.size(),
            std::size(kActionReasons) + std::size(kFeatureReasons));
}

// §38.36.3: the only fields that need to be set for an action or feature
// callback are the reason, the callback routine, and (optionally) user_data.
// Registration succeeds with the remaining fields left at their defaults.
TEST_F(VpiActionFeatureCallbacks, MinimalFieldsSufficeForRegistration) {
  int payload = 0;
  s_cb_data cb = {};
  cb.reason = cbStartOfSimulation;
  cb.cb_rtn = &RecordingCb;
  cb.user_data = &payload;
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);

  const VpiCbData& stored = vpi_ctx_.RegisteredCallbacks().back();
  EXPECT_EQ(stored.reason, cbStartOfSimulation);
  EXPECT_EQ(stored.user_data, &payload);
  EXPECT_EQ(stored.obj, nullptr);
  EXPECT_EQ(stored.time, nullptr);
  EXPECT_EQ(stored.value, nullptr);
  EXPECT_EQ(stored.index, 0);
}

// §38.36.3: when the callback occurs, the application routine is passed a
// pointer to an s_cb_data structure whose reason field holds the reason.
TEST_F(VpiActionFeatureCallbacks, DispatchActionCallbackPassesReason) {
  Register(cbStartOfSimulation);

  int fired = vpi_ctx_.DispatchCallbacks(cbStartOfSimulation);

  EXPECT_EQ(fired, 1);
  EXPECT_EQ(g_invocations, 1);
  EXPECT_EQ(g_seen_reason, cbStartOfSimulation);
}

// §38.36.3: application data placed in user_data reaches the callback routine
// unchanged, since the routine receives the structure supplied at registration.
TEST_F(VpiActionFeatureCallbacks, ExecutingCallbackDeliversUserData) {
  int payload = 7;
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  cb.cb_rtn = &RecordingCb;
  cb.user_data = &payload;
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);

  vpi_ctx_.ExecuteCallback(h);
  EXPECT_EQ(g_seen_user_data, &payload);
}

// §38.36.3: to install a signal handler the application sets the reason to
// cbSignal and the index field to the desired signal number; registration
// preserves that signal number.
TEST_F(VpiActionFeatureCallbacks, SignalCallbackPreservesSignalNumber) {
  s_cb_data cb = {};
  cb.reason = cbSignal;
  cb.cb_rtn = &RecordingCb;
  cb.index = 15;
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);

  const VpiCbData& stored = vpi_ctx_.RegisteredCallbacks().back();
  EXPECT_EQ(stored.reason, cbSignal);
  EXPECT_EQ(stored.index, 15);
}

// §38.36.3: for a cbTchkViolation callback the obj field is a handle to the
// timing check; the simulator supplies it when the callback is delivered.
TEST_F(VpiActionFeatureCallbacks, TchkViolationDeliversTimingCheckHandle) {
  VpiObject timing_check;
  Register(cbTchkViolation);

  int fired = vpi_ctx_.DispatchCallbacks(cbTchkViolation, &timing_check);

  EXPECT_EQ(fired, 1);
  EXPECT_EQ(g_seen_obj, &timing_check);
}

// §38.36.3: for a cbInteractiveScopeChange callback the obj field is a handle
// to the new interactive scope.
TEST_F(VpiActionFeatureCallbacks, InteractiveScopeChangeDeliversScopeHandle) {
  VpiObject scope;
  Register(cbInteractiveScopeChange);

  int fired = vpi_ctx_.DispatchCallbacks(cbInteractiveScopeChange, &scope);

  EXPECT_EQ(fired, 1);
  EXPECT_EQ(g_seen_obj, &scope);
}

// §38.36.3: for a cbUnresolvedSystf callback user_data points to the name of
// the unresolved task or system function.
TEST_F(VpiActionFeatureCallbacks, UnresolvedSystfDeliversName) {
  const char* name = "$unknown_systf";
  Register(cbUnresolvedSystf);

  int fired = vpi_ctx_.DispatchCallbacks(cbUnresolvedSystf, nullptr,
                                         const_cast<char*>(name));

  EXPECT_EQ(fired, 1);
  EXPECT_EQ(g_seen_user_data, name);
}

// §38.36.3: a reset delivers cbStartOfReset at the start of the operation and
// cbEndOfReset after it has completed, in that order.
TEST_F(VpiActionFeatureCallbacks, ResetDeliversStartThenEnd) {
  Register(cbEndOfReset);
  Register(cbStartOfReset);

  int fired = vpi_ctx_.DispatchReset();

  EXPECT_EQ(fired, 2);
  ASSERT_EQ(g_sequence.size(), 2u);
  EXPECT_EQ(g_sequence[0], cbStartOfReset);
  EXPECT_EQ(g_sequence[1], cbEndOfReset);
}

// §38.36.3: a restart removes every callback other than the restart callbacks
// and then delivers cbStartOfRestart followed by cbEndOfRestart, so that the
// only callbacks that exist across the restart are those two. This observes
// both halves of the rule: several varied non-restart callbacks are all purged,
// while the restart pair both survives and is delivered.
TEST_F(VpiActionFeatureCallbacks,
       RestartPurgesOthersAndDeliversRestartCallbacks) {
  Register(cbValueChange);
  Register(cbStmt);
  Register(cbStartOfSave);
  vpiHandle start_restart = Register(cbStartOfRestart);
  vpiHandle end_restart = Register(cbEndOfRestart);
  ASSERT_NE(start_restart, nullptr);
  ASSERT_NE(end_restart, nullptr);

  int fired = vpi_ctx_.DispatchRestart();

  // Only the two restart callbacks are delivered, start before end.
  EXPECT_EQ(fired, 2);
  ASSERT_EQ(g_sequence.size(), 2u);
  EXPECT_EQ(g_sequence[0], cbStartOfRestart);
  EXPECT_EQ(g_sequence[1], cbEndOfRestart);

  // After the restart, the surviving callbacks are exactly the restart pair:
  // every other reason has been removed (RemoveCb clears the reason to -1), and
  // both restart reasons remain present.
  std::multiset<int> survivors;
  for (const VpiCbData& cb : vpi_ctx_.RegisteredCallbacks()) {
    if (cb.reason != -1) survivors.insert(cb.reason);
  }
  std::multiset<int> expected{cbStartOfRestart, cbEndOfRestart};
  EXPECT_EQ(survivors, expected);
}

// §38.36.3: the reset callbacks occur whether the reset is invoked directly or
// indirectly through vpi_control(vpiReset, ...). Driving the reset through the
// C control entry point delivers the same start-then-end sequence.
TEST_F(VpiActionFeatureCallbacks, ResetViaVpiControlDeliversCallbacks) {
  Register(cbStartOfReset);
  Register(cbEndOfReset);

  int handled = VpiControlC(vpiReset, 0);

  EXPECT_EQ(handled, 1);
  ASSERT_EQ(g_sequence.size(), 2u);
  EXPECT_EQ(g_sequence[0], cbStartOfReset);
  EXPECT_EQ(g_sequence[1], cbEndOfReset);
}

// §38.36.3 (edge case): dispatching a reason with no registered callback
// invokes no application routine and reports zero deliveries.
TEST_F(VpiActionFeatureCallbacks, DispatchWithNoMatchingCallbackFiresNothing) {
  Register(cbStartOfSimulation);

  int fired = vpi_ctx_.DispatchCallbacks(cbEndOfCompile);

  EXPECT_EQ(fired, 0);
  EXPECT_EQ(g_invocations, 0);
}

// §38.36.3 (edge case): a callback removed before dispatch is not delivered, so
// only the still-registered callback for the reason runs.
TEST_F(VpiActionFeatureCallbacks, RemovedCallbackIsNotDispatched) {
  vpiHandle removed = Register(cbStartOfSimulation);
  Register(cbStartOfSimulation);
  ASSERT_NE(removed, nullptr);
  ASSERT_EQ(VpiRemoveCbC(removed), 1);

  int fired = vpi_ctx_.DispatchCallbacks(cbStartOfSimulation);

  EXPECT_EQ(fired, 1);
  EXPECT_EQ(g_invocations, 1);
}

}  // namespace
}  // namespace delta
