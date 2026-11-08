#include <gtest/gtest.h>

#include <cstddef>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_data_structs.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

extern "C" {
vpiHandle vpi_iterate_1364v1995(PLI_INT32 type, vpiHandle ref);
vpiHandle vpi_iterate_1800v2012(PLI_INT32 type, vpiHandle ref);
}

namespace delta {
namespace {

VpiToolPhase g_phase_during_routine = VpiToolPhase::kFull;
bool g_routine_systf_registered = false;
bool g_routine_allowed_cb_registered = false;
bool g_routine_illegal_cb_registered = false;

int NoopCb(s_cb_data*) { return 0; }

void StartupRoutine() {
  g_phase_during_routine = GetGlobalVpiContext().ToolPhase();

  s_vpi_systf_data systf = {};
  systf.type = vpiSysTask;
  systf.tfname = VpiText("$my_task");
  g_routine_systf_registered = vpi_register_systf(&systf) != nullptr;

  s_cb_data ok = {};
  ok.reason = cbEndOfCompile;
  ok.cb_rtn = NoopCb;
  g_routine_allowed_cb_registered = vpi_register_cb(&ok) != nullptr;

  VpiObject watched;
  watched.type = vpiReg;
  s_cb_data bad = {};
  bad.reason = cbValueChange;
  bad.cb_rtn = NoopCb;
  bad.obj = VpiHandleOf(&watched);
  g_routine_illegal_cb_registered = vpi_register_cb(&bad) != nullptr;
}

class VpiFunctionAvailability : public ::testing::Test {
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

TEST_F(VpiFunctionAvailability, OnlyRegistrationRoutinesAvailableInStartup) {
  EXPECT_TRUE(VpiRoutineAvailableInStartup(VpiRoutine::kRegisterSystf));
  EXPECT_TRUE(VpiRoutineAvailableInStartup(VpiRoutine::kRegisterCb));
  EXPECT_FALSE(VpiRoutineAvailableInStartup(VpiRoutine::kGetValue));
  EXPECT_FALSE(VpiRoutineAvailableInStartup(VpiRoutine::kPutValue));
  EXPECT_FALSE(VpiRoutineAvailableInStartup(VpiRoutine::kIterate));
}

TEST_F(VpiFunctionAvailability, OnlyFullPhaseIsUnrestricted) {
  EXPECT_TRUE(VpiPhaseRestrictsFunctionality(VpiToolPhase::kStartup));
  EXPECT_TRUE(VpiPhaseRestrictsFunctionality(VpiToolPhase::kSizetf));
  EXPECT_FALSE(VpiPhaseRestrictsFunctionality(VpiToolPhase::kFull));
}

TEST_F(VpiFunctionAvailability, StartupCallbackReasonSetIsTheSixReasons) {
  EXPECT_TRUE(VpiStartupCallbackReasonAllowed(cbEndOfCompile));
  EXPECT_TRUE(VpiStartupCallbackReasonAllowed(cbStartOfSimulation));
  EXPECT_TRUE(VpiStartupCallbackReasonAllowed(cbEndOfSimulation));
  EXPECT_TRUE(VpiStartupCallbackReasonAllowed(cbUnresolvedSystf));
  EXPECT_TRUE(VpiStartupCallbackReasonAllowed(cbError));
  EXPECT_TRUE(VpiStartupCallbackReasonAllowed(cbPLIError));

  EXPECT_FALSE(VpiStartupCallbackReasonAllowed(cbValueChange));
  EXPECT_FALSE(VpiStartupCallbackReasonAllowed(cbReadWriteSynch));
  EXPECT_FALSE(VpiStartupCallbackReasonAllowed(cbStmt));
  EXPECT_FALSE(VpiStartupCallbackReasonAllowed(cbAfterDelay));
}

TEST_F(VpiFunctionAvailability, RegisterCbAcceptsEarlyReasonsInStartup) {
  vpi_ctx_.SetToolPhase(VpiToolPhase::kStartup);
  const int kReasons[] = {cbEndOfCompile,    cbStartOfSimulation,
                          cbEndOfSimulation, cbUnresolvedSystf,
                          cbError,           cbPLIError};
  for (int reason : kReasons) {
    s_cb_data cb = {};
    cb.reason = reason;
    cb.cb_rtn = NoopCb;
    EXPECT_NE(vpi_register_cb(&cb), nullptr) << "reason " << reason;
  }
}

TEST_F(VpiFunctionAvailability, RegisterCbRejectsOtherReasonInStartup) {
  vpi_ctx_.SetToolPhase(VpiToolPhase::kStartup);
  size_t before = vpi_ctx_.RegisteredCallbacks().size();

  VpiObject watched;
  watched.type = vpiReg;
  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.cb_rtn = NoopCb;
  cb.obj = VpiHandleOf(&watched);
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);
  EXPECT_EQ(vpi_ctx_.RegisteredCallbacks().size(), before);
  EXPECT_EQ(vpi_ctx_.LastError().level, vpiError);
}

TEST_F(VpiFunctionAvailability, RegisterCbRejectsOtherReasonInSizetfPhase) {
  vpi_ctx_.SetToolPhase(VpiToolPhase::kSizetf);
  VpiObject stmt;
  stmt.type = vpiAssignment;
  s_cb_data cb = {};
  cb.reason = cbStmt;
  cb.cb_rtn = NoopCb;
  cb.obj = VpiHandleOf(&stmt);
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);
}

TEST_F(VpiFunctionAvailability, RegisterCbAcceptsAnyReasonInFullPhase) {
  vpi_ctx_.SetToolPhase(VpiToolPhase::kFull);
  VpiObject watched;
  watched.type = vpiReg;
  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.cb_rtn = NoopCb;
  cb.obj = VpiHandleOf(&watched);
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

TEST_F(VpiFunctionAvailability, StartupWalkEstablishesAndRestoresPhase) {
  g_phase_during_routine = VpiToolPhase::kFull;
  g_routine_systf_registered = false;
  g_routine_allowed_cb_registered = false;
  g_routine_illegal_cb_registered = false;

  VlogStartupRoutine routines[] = {&StartupRoutine, nullptr};
  InvokeVlogStartupRoutines(routines);

  EXPECT_EQ(g_phase_during_routine, VpiToolPhase::kStartup);
  EXPECT_TRUE(g_routine_systf_registered);
  EXPECT_TRUE(g_routine_allowed_cb_registered);
  EXPECT_FALSE(g_routine_illegal_cb_registered);
  EXPECT_EQ(vpi_ctx_.ToolPhase(), VpiToolPhase::kFull);
}

TEST_F(VpiFunctionAvailability, IterateIsRefusedDuringStartup) {
  vpi_ctx_.SetToolPhase(VpiToolPhase::kStartup);

  EXPECT_EQ(vpi_iterate(vpiModule, nullptr), nullptr);

  s_vpi_error_info info = {};
  EXPECT_NE(vpi_chk_error(&info), 0);
  EXPECT_STREQ(info.message,
               "VPI routine is not available until cbEndOfCompile; only "
               "vpi_register_systf() and vpi_register_cb() may be called "
               "before then");
}

TEST_F(VpiFunctionAvailability, IterateIsRefusedDuringTheSizetfPhase) {
  vpi_ctx_.SetToolPhase(VpiToolPhase::kSizetf);

  EXPECT_EQ(vpi_iterate(vpiModule, nullptr), nullptr);
  EXPECT_NE(vpi_chk_error(nullptr), 0);
}

TEST_F(VpiFunctionAvailability, TheFullPhaseRefusesNothingAndStartupSparesTwo) {
  vpi_ctx_.SetToolPhase(VpiToolPhase::kFull);
  EXPECT_FALSE(vpi_ctx_.RoutineIsUnavailableNow(VpiRoutine::kIterate));
  EXPECT_FALSE(vpi_ctx_.RoutineIsUnavailableNow(VpiRoutine::kGetValue));
  EXPECT_FALSE(vpi_ctx_.RoutineIsUnavailableNow(VpiRoutine::kPutValue));

  vpi_ctx_.SetToolPhase(VpiToolPhase::kStartup);
  EXPECT_FALSE(vpi_ctx_.RoutineIsUnavailableNow(VpiRoutine::kRegisterSystf));
  EXPECT_FALSE(vpi_ctx_.RoutineIsUnavailableNow(VpiRoutine::kRegisterCb));
  EXPECT_TRUE(vpi_ctx_.RoutineIsUnavailableNow(VpiRoutine::kIterate));
}

TEST_F(VpiFunctionAvailability, GetValueIsRefusedDuringStartup) {
  vpi_ctx_.SetToolPhase(VpiToolPhase::kStartup);

  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 4321;
  vpi_get_value(nullptr, &value);

  EXPECT_EQ(value.value.integer, 4321);
  EXPECT_NE(vpi_chk_error(nullptr), 0);
}

TEST_F(VpiFunctionAvailability, PutValueIsRefusedDuringStartup) {
  vpi_ctx_.SetToolPhase(VpiToolPhase::kStartup);

  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 1;
  EXPECT_EQ(vpi_put_value(nullptr, &value, nullptr, vpiNoDelay), nullptr);
  EXPECT_NE(vpi_chk_error(nullptr), 0);
}

TEST_F(VpiFunctionAvailability,
       ACompatibilityModeIterateIsRefusedDuringStartup) {
  vpi_ctx_.SetToolPhase(VpiToolPhase::kStartup);

  EXPECT_EQ(vpi_iterate_1364v1995(vpiModule, nullptr), nullptr);
  EXPECT_NE(vpi_chk_error(nullptr), 0);
  vpi_ctx_.ResetErrorStatus();
  EXPECT_EQ(vpi_iterate_1800v2012(vpiModule, nullptr), nullptr);
  EXPECT_NE(vpi_chk_error(nullptr), 0);
}

}  // namespace
}  // namespace delta
