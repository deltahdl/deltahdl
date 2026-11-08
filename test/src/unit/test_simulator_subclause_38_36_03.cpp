#include <gtest/gtest.h>

#include <csignal>
#include <iterator>
#include <set>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_simulator.h"
#include "helpers_event_callbacks.h"
#include "helpers_reported_error.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/specify.h"
#include "simulator/specify_path_delay.h"
#include "simulator/specify_timing_check.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_signal_callbacks.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

int g_invocations = 0;
int g_seen_reason = 0;
void* g_seen_user_data = nullptr;
VpiHandle g_seen_obj = nullptr;
std::vector<int> g_sequence;

int RecordingCb(s_cb_data* data) {
  ++g_invocations;
  if (data) {
    g_seen_reason = data->reason;
    g_seen_user_data = data->user_data;
    g_seen_obj = VpiObjectOf(data->obj);
    g_sequence.push_back(data->reason);
  }
  return 0;
}

const int kActionReasons[] = {
    cbEndOfCompile, cbStartOfSimulation, cbEndOfSimulation, cbError,
    cbPLIError,     cbTchkViolation,     cbSignal,
};

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

  vpiHandle Register(int reason, VpiObject* on = nullptr) {
    s_cb_data cb = {};
    cb.reason = reason;
    cb.cb_rtn = &RecordingCb;
    cb.obj = VpiHandleOf(on);
    return vpi_register_cb(&cb);
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

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

TEST_F(VpiActionFeatureCallbacks, ReasonCodesAreDistinct) {
  std::set<int> seen;
  for (int reason : kActionReasons) seen.insert(reason);
  for (int reason : kFeatureReasons) seen.insert(reason);
  EXPECT_EQ(seen.size(),
            std::size(kActionReasons) + std::size(kFeatureReasons));
}

TEST_F(VpiActionFeatureCallbacks, MinimalFieldsSufficeForRegistration) {
  int payload = 0;
  s_cb_data cb = {};
  cb.reason = cbStartOfSimulation;
  cb.cb_rtn = &RecordingCb;
  cb.user_data = reinterpret_cast<PLI_BYTE8*>(&payload);
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);

  const s_cb_data& stored = vpi_ctx_.RegisteredCallbacks().back();
  EXPECT_EQ(stored.reason, cbStartOfSimulation);
  EXPECT_EQ(stored.user_data, reinterpret_cast<PLI_BYTE8*>(&payload));
  EXPECT_EQ(stored.obj, nullptr);
  EXPECT_EQ(stored.time, nullptr);
  EXPECT_EQ(stored.value, nullptr);
  EXPECT_EQ(stored.index, 0);
}

TEST_F(VpiActionFeatureCallbacks, DispatchActionCallbackPassesReason) {
  Register(cbStartOfSimulation);

  int fired = vpi_ctx_.DispatchCallbacks(cbStartOfSimulation);

  EXPECT_EQ(fired, 1);
  EXPECT_EQ(g_invocations, 1);
  EXPECT_EQ(g_seen_reason, cbStartOfSimulation);
}

TEST_F(VpiActionFeatureCallbacks, ExecutingCallbackDeliversUserData) {
  int payload = 7;
  s_cb_data cb = {};
  cb.reason = cbEndOfSimulation;
  cb.cb_rtn = &RecordingCb;
  cb.user_data = reinterpret_cast<PLI_BYTE8*>(&payload);
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);

  vpi_ctx_.ExecuteCallback(VpiObjectOf(h));
  EXPECT_EQ(g_seen_user_data, &payload);
}

TEST_F(VpiActionFeatureCallbacks, SignalCallbackPreservesSignalNumber) {
  s_cb_data cb = {};
  cb.reason = cbSignal;
  cb.cb_rtn = &RecordingCb;
  cb.index = 15;
  vpiHandle h = vpi_register_cb(&cb);
  ASSERT_NE(h, nullptr);

  const s_cb_data& stored = vpi_ctx_.RegisteredCallbacks().back();
  EXPECT_EQ(stored.reason, cbSignal);
  EXPECT_EQ(stored.index, 15);
}

TEST_F(VpiActionFeatureCallbacks, ARaisedSignalCallsOnlyItsOwnCallbacks) {
  s_cb_data asked = {};
  asked.reason = cbSignal;
  asked.cb_rtn = &RecordingCb;
  asked.index = SIGINT;
  vpiHandle own = vpi_register_cb(&asked);
  asked.index = SIGILL;
  vpiHandle other = vpi_register_cb(&asked);
  asked.index = SIGINT;
  asked.cb_rtn = nullptr;
  vpiHandle routineless = vpi_register_cb(&asked);
  std::raise(SIGINT);
  EXPECT_EQ(vpi_ctx_.DeliverRaisedSignals(), 1);
  EXPECT_EQ(g_invocations, 1);
  EXPECT_EQ(g_seen_reason, cbSignal);
  for (vpiHandle cb : {own, other, routineless}) {
    EXPECT_EQ(vpi_remove_cb(cb), 1);
  }
}

TEST_F(VpiActionFeatureCallbacks, TchkViolationDeliversTimingCheckHandle) {
  VpiObject timing_check;
  Register(cbTchkViolation);

  int fired = vpi_ctx_.DispatchCallbacks(cbTchkViolation, &timing_check);

  EXPECT_EQ(fired, 1);
  EXPECT_EQ(g_seen_obj, &timing_check);
}

TEST_F(VpiActionFeatureCallbacks,
       TchkViolationOfARunWithNoChecksReachesNoTchk) {
  Register(cbTchkViolation);
  vpi_ctx_.Attach(sim_ctx_);
  TimingCheckEntry stray;
  vpi_ctx_.NoteTimingViolation(stray);
  EXPECT_EQ(g_invocations, 0);
}

TEST_F(VpiActionFeatureCallbacks, TchkViolationReachesTheTchkOfTheCheck) {
  SpecifyManager& specify = sim_ctx_.AcquireSpecifyManager();
  PathDelay path;
  path.inst_prefix = "u.";
  specify.MutablePathDelays().push_back(path);
  TimingCheckEntry check;
  check.inst_prefix = "u.";
  specify.MutableTimingChecks() = {check, check};
  Register(cbTchkViolation);
  vpi_ctx_.Attach(sim_ctx_);
  specify.MutableTimingChecks().push_back(check);
  std::vector<VpiHandle> tchks;
  vpiHandle it =
      vpi_iterate(vpiTchk, vpi_handle_by_name(VpiText("u"), nullptr));
  for (vpiHandle tchk = it ? vpi_scan(it) : nullptr; tchk != nullptr;
       tchk = vpi_scan(it)) {
    tchks.push_back(VpiObjectOf(tchk));
  }
  ASSERT_EQ(tchks.size(), 2u);

  vpi_ctx_.NoteTimingViolation(specify.GetTimingChecks()[1]);
  EXPECT_EQ(g_invocations, 1);
  EXPECT_EQ(g_seen_obj, tchks[1]);
  vpi_ctx_.NoteTimingViolation(specify.GetTimingChecks()[2]);
  EXPECT_EQ(g_invocations, 1);
}

TEST_F(VpiActionFeatureCallbacks, InteractiveScopeChangeDeliversScopeHandle) {
  VpiObject scope;
  Register(cbInteractiveScopeChange);

  int fired = vpi_ctx_.DispatchCallbacks(cbInteractiveScopeChange, &scope);

  EXPECT_EQ(fired, 1);
  EXPECT_EQ(g_seen_obj, &scope);
}

TEST_F(VpiActionFeatureCallbacks, UnresolvedSystfDeliversName) {
  const char* name = "$unknown_systf";
  Register(cbUnresolvedSystf);

  int fired = vpi_ctx_.DispatchCallbacks(cbUnresolvedSystf, nullptr,
                                         const_cast<char*>(name));

  EXPECT_EQ(fired, 1);
  EXPECT_EQ(g_seen_user_data, name);
}

TEST_F(VpiActionFeatureCallbacks, ResetDeliversStartThenEnd) {
  Register(cbEndOfReset);
  Register(cbStartOfReset);

  int fired = vpi_ctx_.DispatchReset();

  EXPECT_EQ(fired, 2);
  ASSERT_EQ(g_sequence.size(), 2u);
  EXPECT_EQ(g_sequence[0], cbStartOfReset);
  EXPECT_EQ(g_sequence[1], cbEndOfReset);
}

TEST_F(VpiActionFeatureCallbacks,
       RestartPurgesOthersAndDeliversRestartCallbacks) {
  VpiObject watched;
  watched.type = vpiReg;
  VpiObject stmt;
  stmt.type = vpiAssignment;
  ASSERT_NE(Register(cbValueChange, &watched), nullptr);
  ASSERT_NE(Register(cbStmt, &stmt), nullptr);
  ASSERT_NE(Register(cbStartOfSave), nullptr);
  vpiHandle start_restart = Register(cbStartOfRestart);
  vpiHandle end_restart = Register(cbEndOfRestart);
  ASSERT_NE(start_restart, nullptr);
  ASSERT_NE(end_restart, nullptr);

  int fired = vpi_ctx_.DispatchRestart();

  EXPECT_EQ(fired, 2);
  ASSERT_EQ(g_sequence.size(), 2u);
  EXPECT_EQ(g_sequence[0], cbStartOfRestart);
  EXPECT_EQ(g_sequence[1], cbEndOfRestart);

  std::multiset<int> survivors;
  for (const s_cb_data& cb : vpi_ctx_.RegisteredCallbacks()) {
    if (cb.reason != -1) survivors.insert(cb.reason);
  }
  std::multiset<int> expected{cbStartOfRestart, cbEndOfRestart};
  EXPECT_EQ(survivors, expected);
}

TEST_F(VpiActionFeatureCallbacks,
       ResetViaVpiControlFailsAndDeliversNoCallback) {
  Register(cbStartOfReset);
  Register(cbEndOfReset);

  int handled = vpi_control(vpiReset, 0, 0, 0);

  EXPECT_EQ(handled, 0);
  EXPECT_TRUE(g_sequence.empty());
}

TEST_F(VpiActionFeatureCallbacks, DispatchWithNoMatchingCallbackFiresNothing) {
  Register(cbStartOfSimulation);

  int fired = vpi_ctx_.DispatchCallbacks(cbEndOfCompile);

  EXPECT_EQ(fired, 0);
  EXPECT_EQ(g_invocations, 0);
}

TEST_F(VpiActionFeatureCallbacks, RemovedCallbackIsNotDispatched) {
  vpiHandle removed = Register(cbStartOfSimulation);
  Register(cbStartOfSimulation);
  ASSERT_NE(removed, nullptr);
  ASSERT_EQ(vpi_remove_cb(removed), 1);

  int fired = vpi_ctx_.DispatchCallbacks(cbStartOfSimulation);

  EXPECT_EQ(fired, 1);
  EXPECT_EQ(g_invocations, 1);
}

std::vector<int> g_action_order;

int RecordEndOfCompile(s_cb_data*) {
  g_action_order.push_back(cbEndOfCompile);
  return 0;
}

int RecordStartOfSimulation(s_cb_data*) {
  g_action_order.push_back(cbStartOfSimulation);
  return 0;
}

int RecordEndOfSimulation(s_cb_data*) {
  g_action_order.push_back(cbEndOfSimulation);
  return 0;
}

void RegisterLifetimeCallbacks() {
  g_action_order.clear();

  s_cb_data compiled = {};
  compiled.reason = cbEndOfCompile;
  compiled.cb_rtn = &RecordEndOfCompile;
  ASSERT_NE(vpi_register_cb(&compiled), nullptr);

  s_cb_data started = {};
  started.reason = cbStartOfSimulation;
  started.cb_rtn = &RecordStartOfSimulation;
  ASSERT_NE(vpi_register_cb(&started), nullptr);

  s_cb_data ended = {};
  ended.reason = cbEndOfSimulation;
  ended.cb_rtn = &RecordEndOfSimulation;
  ASSERT_NE(vpi_register_cb(&ended), nullptr);
}

class VpiLifetimeCallbacksInARun : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(VpiLifetimeCallbacksInARun, TheThreeLifetimeActionsOccurInOrder) {
  RegisterLifetimeCallbacks();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int r;\n"
      "  initial r = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  f.scheduler.EndSimulation();

  EXPECT_EQ(g_action_order,
            (std::vector<int>{cbEndOfCompile, cbStartOfSimulation,
                              cbEndOfSimulation}));
}

TEST_F(VpiLifetimeCallbacksInARun, TheEndOfSimulationActionOccursAfterAFinish) {
  RegisterLifetimeCallbacks();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  initial begin\n"
      "    #5 $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  f.scheduler.EndSimulation();

  ASSERT_FALSE(g_action_order.empty());
  EXPECT_EQ(g_action_order.back(), cbEndOfSimulation);
}

std::vector<std::string>& UnresolvedNames() {
  static std::vector<std::string> names;
  return names;
}

PLI_INT32 RecordUnresolvedName(p_cb_data cb) {
  UnresolvedNames().emplace_back(cb->user_data);
  return 0;
}

TEST(UnresolvedSystfOfARun, AnUnknownSystemTaskIsReportedToTheApplication) {
  UnresolvedNames().clear();
  VpiContext vpi;
  SetGlobalVpiContext(&vpi);
  s_cb_data data = {};
  data.reason = cbUnresolvedSystf;
  data.cb_rtn = &RecordUnresolvedName;
  ASSERT_NE(vpi_register_cb(&data), nullptr);
  SimFixture f;
  auto* design = ElaborateSrc(
      "module top; initial $nobody_registered_this; endmodule\n", f);
  if (design != nullptr) LowerAndRun(design, f);
  SetGlobalVpiContext(nullptr);
  EXPECT_EQ(UnresolvedNames(),
            (std::vector<std::string>{"$nobody_registered_this"}));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$nobody_registered_this is not a system task or "
                            "system function this tool implements",
                            1, "20.1"));
}

int violated_tchk_type = 0;

PLI_INT32 RecordViolatedCheck(p_cb_data cb) {
  violated_tchk_type = vpi_get(vpiTchkType, cb->obj);
  return RecordEventDelivery(cb);
}

TEST_F(EventCallbacksOfARun, ATchkViolationCallbackIsGivenTheCheck) {
  violated_tchk_type = 0;
  Armer() = [] {
    s_cb_data data = {};
    data.reason = cbTchkViolation;
    data.cb_rtn = &RecordViolatedCheck;
    vpi_register_cb(&data);
  };
  Run("module top(output logic d, output logic clk);\n"
      "  timeunit 1ns; timeprecision 1ns;\n"
      "  specify\n"
      "    $setup(d, posedge clk, 5);\n"
      "  endspecify\n"
      "  initial begin $arm; d = 0; clk = 0; #10 d = 1; #2 clk = 1; end\n"
      "endmodule\n");
  const std::vector<EventDelivery> kViolations = DeliveriesOf(cbTchkViolation);
  ASSERT_EQ(kViolations.size(), 1u);
  EXPECT_EQ(kViolations[0].obj_type, vpiTchk);
  EXPECT_EQ(kViolations[0].now, 12u);
  EXPECT_EQ(violated_tchk_type, vpiSetup);
}

TEST_F(EventCallbacksOfARun, ADirectResetCallsNoResetCallback) {
  Armer() = [] {
    PlaceEventCallback(cbStartOfReset, nullptr);
    PlaceEventCallback(cbEndOfReset, nullptr);
  };
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  initial begin $arm; #5 $reset; end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(f_.diag.Diagnostics(),
                            "$reset is the optional system task or system "
                            "function D.8 describes, which Annex D.1 allows "
                            "an implementation to be without; this "
                            "implementation is one without it",
                            2, "D.1"));
  EXPECT_TRUE(EventDeliveries().empty());
}

TEST_F(EventCallbacksOfARun, AScopeTaskCallsTheScopeChangeCallback) {
  Armer() = [] { PlaceEventCallback(cbInteractiveScopeChange, nullptr); };
  Run("module top; timeunit 1ns; timeprecision 1ns;\n"
      "  initial begin $arm; #1 $scope(top.blk); end\n"
      "  initial begin : blk #2; end\n"
      "endmodule\n");
  const std::vector<EventDelivery> kChanges =
      DeliveriesOf(cbInteractiveScopeChange);
  ASSERT_EQ(kChanges.size(), 1u);
  EXPECT_EQ(kChanges[0].obj, "blk");
  EXPECT_EQ(kChanges[0].now, 1u);
}

TEST_F(EventCallbacksOfARun, SettingTheScopeCallsTheScopeChangeCallback) {
  Armer() = [] {
    PlaceEventCallback(cbInteractiveScopeChange, nullptr);
    vpi_control(vpiSetInteractiveScope, TopObject("top.blk"));
  };
  Run("module top;\n"
      "  initial $arm;\n"
      "  initial begin : blk #2; end\n"
      "endmodule\n");
  const std::vector<EventDelivery> kChanges =
      DeliveriesOf(cbInteractiveScopeChange);
  ASSERT_EQ(kChanges.size(), 1u);
  EXPECT_EQ(kChanges[0].obj, "blk");
}

vpiHandle signal_callback = nullptr;

TEST_F(EventCallbacksOfARun, ASignalCallbackIsCalledAndTheRunGoesOn) {
  Armer() = [] {
    PlaceEventCallback(cbStartOfReset, nullptr);
    s_cb_data data = {};
    data.reason = cbSignal;
    data.index = SIGTERM;
    data.cb_rtn = &RecordEventDelivery;
    signal_callback = vpi_register_cb(&data);
    std::raise(SIGTERM);
  };
  Run("module top; timeunit 1ns; timeprecision 1ns; int after = 0;\n"
      "  initial begin $arm; #1 after = 1; end\n"
      "endmodule\n");
  const std::vector<EventDelivery> kSignals = DeliveriesOf(cbSignal);
  ASSERT_EQ(kSignals.size(), 1u);
  EXPECT_EQ(kSignals[0].index, SIGTERM);
  s_vpi_value after = {};
  after.format = vpiIntVal;
  vpi_get_value(TopObject("top.after"), &after);
  EXPECT_EQ(after.value.integer, 1);
  EXPECT_EQ(vpi_remove_cb(signal_callback), 1);
}

TEST(VpiSignalTraps, ASignalIsTrappedWhileAskedFor) {
  VpiTrapSignal(0);
  VpiTrapSignal(SIGINT);
  VpiTrapSignal(SIGINT);
  std::vector<s_cb_data> asked(1);
  asked[0].reason = cbSignal;
  asked[0].index = SIGINT;
  VpiReleaseSignal(SIGINT, asked);
  EXPECT_TRUE(VpiTakeRaisedSignals().empty());
  std::raise(SIGINT);
  EXPECT_EQ(VpiTakeRaisedSignals(), std::vector<int>{SIGINT});
  VpiReleaseSignal(SIGINT, {});
  VpiReleaseSignal(0, {});
}

TEST(VpiSignalTraps, ASignalNoTrapCanHoldIsLeftAlone) {
  constexpr int kUncatchable = 9;
  VpiTrapSignal(65);
  VpiTrapSignal(kUncatchable);
  VpiReleaseSignal(65, {});
  VpiReleaseSignal(kUncatchable, {});
  VpiReleaseSignal(SIGSEGV, {});
  EXPECT_TRUE(VpiTakeRaisedSignals().empty());
}

}  // namespace
}  // namespace delta

extern "C" {
static volatile std::sig_atomic_t g_abort_handled = 0;
static void NoteAbort(int) { g_abort_handled = 1; }
}

namespace delta {
namespace {

TEST(VpiSignalTraps, ReleasingASignalRestoresItsEarlierHandler) {
  std::signal(SIGABRT, &NoteAbort);
  VpiTrapSignal(SIGABRT);
  std::raise(SIGABRT);
  EXPECT_EQ(VpiTakeRaisedSignals(), std::vector<int>{SIGABRT});
  EXPECT_EQ(g_abort_handled, 0);
  std::vector<s_cb_data> asked(1);
  asked[0].reason = cbSignal;
  asked[0].index = SIGILL;
  VpiReleaseSignal(SIGABRT, asked);
  std::raise(SIGABRT);
  EXPECT_EQ(g_abort_handled, 1);
  EXPECT_TRUE(VpiTakeRaisedSignals().empty());
  std::signal(SIGABRT, SIG_DFL);
}

}  // namespace
}  // namespace delta
