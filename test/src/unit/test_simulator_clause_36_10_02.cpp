#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §36.10.2: a startup routine records the tool phase it observes while it runs,
// and exercises the two routines that are available during the startup phase.
VpiToolPhase g_phase_during_routine = VpiToolPhase::kFull;
bool g_routine_systf_registered = false;
bool g_routine_allowed_cb_registered = false;
bool g_routine_illegal_cb_registered = false;

int NoopCb(VpiCbData*) { return 0; }

void StartupRoutine() {
  g_phase_during_routine = GetGlobalVpiContext().ToolPhase();

  // Both registration routines are available in the startup phase.
  s_vpi_systf_data systf = {};
  systf.type = vpiSysTask;
  systf.tfname = "$my_task";
  g_routine_systf_registered = vpi_register_systf(&systf) != nullptr;

  // A callback for an early-phase reason is accepted...
  s_cb_data ok = {};
  ok.reason = cbEndOfCompile;
  ok.cb_rtn = NoopCb;
  g_routine_allowed_cb_registered = vpi_register_cb(&ok) != nullptr;

  // ...while a callback for any other reason is refused during startup.
  s_cb_data bad = {};
  bad.reason = cbValueChange;
  bad.cb_rtn = NoopCb;
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

// §36.10.2 (C2): only the two registration routines are available while the
// vlog_startup_routines[] array executes; every other routine is not.
TEST_F(VpiFunctionAvailability, OnlyRegistrationRoutinesAvailableInStartup) {
  EXPECT_TRUE(VpiRoutineAvailableInStartup(VpiRoutine::kRegisterSystf));
  EXPECT_TRUE(VpiRoutineAvailableInStartup(VpiRoutine::kRegisterCb));
  EXPECT_FALSE(VpiRoutineAvailableInStartup(VpiRoutine::kGetValue));
  EXPECT_FALSE(VpiRoutineAvailableInStartup(VpiRoutine::kPutValue));
  EXPECT_FALSE(VpiRoutineAvailableInStartup(VpiRoutine::kIterate));
}

// §36.10.2 (C5/C6): the startup and sizetf phases restrict functionality; only
// the full phase makes all functionality available.
TEST_F(VpiFunctionAvailability, OnlyFullPhaseIsUnrestricted) {
  EXPECT_TRUE(VpiPhaseRestrictsFunctionality(VpiToolPhase::kStartup));
  EXPECT_TRUE(VpiPhaseRestrictsFunctionality(VpiToolPhase::kSizetf));
  EXPECT_FALSE(VpiPhaseRestrictsFunctionality(VpiToolPhase::kFull));
}

// §36.10.2 (C3): exactly the six early-phase reasons are allowed; nothing else.
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

// §36.10.2 (C3): in the startup phase, vpi_register_cb() accepts every one of
// the six early-phase reasons.
TEST_F(VpiFunctionAvailability, RegisterCbAcceptsEarlyReasonsInStartup) {
  vpi_ctx_.SetToolPhase(VpiToolPhase::kStartup);
  const int reasons[] = {cbEndOfCompile,    cbStartOfSimulation,
                         cbEndOfSimulation, cbUnresolvedSystf,
                         cbError,           cbPLIError};
  for (int reason : reasons) {
    s_cb_data cb = {};
    cb.reason = reason;
    cb.cb_rtn = NoopCb;
    EXPECT_NE(vpi_register_cb(&cb), nullptr) << "reason " << reason;
  }
}

// §36.10.2 (C3): a non-early-phase reason is refused during startup, with an
// error recorded and no callback added.
TEST_F(VpiFunctionAvailability, RegisterCbRejectsOtherReasonInStartup) {
  vpi_ctx_.SetToolPhase(VpiToolPhase::kStartup);
  size_t before = vpi_ctx_.RegisteredCallbacks().size();

  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.cb_rtn = NoopCb;
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);
  EXPECT_EQ(vpi_ctx_.RegisteredCallbacks().size(), before);
  EXPECT_EQ(vpi_ctx_.LastError().level, vpiError);
}

// §36.10.2 (C5): the sizetf phase permits no access beyond the startup phase,
// so the same callback-reason restriction is in force.
TEST_F(VpiFunctionAvailability, RegisterCbRejectsOtherReasonInSizetfPhase) {
  vpi_ctx_.SetToolPhase(VpiToolPhase::kSizetf);
  s_cb_data cb = {};
  cb.reason = cbStmt;
  cb.cb_rtn = NoopCb;
  EXPECT_EQ(vpi_register_cb(&cb), nullptr);
}

// §36.10.2 (C6): once the full phase is reached, the restriction is lifted and
// any callback reason is accepted.
TEST_F(VpiFunctionAvailability, RegisterCbAcceptsAnyReasonInFullPhase) {
  vpi_ctx_.SetToolPhase(VpiToolPhase::kFull);
  s_cb_data cb = {};
  cb.reason = cbValueChange;
  cb.cb_rtn = NoopCb;
  EXPECT_NE(vpi_register_cb(&cb), nullptr);
}

// §36.10.2 (C2/C5/C6 end to end): walking vlog_startup_routines[] runs the
// routines in the startup phase, where the registration routines work and an
// illegal callback reason is refused, and restores the full phase afterwards.
TEST_F(VpiFunctionAvailability, StartupWalkEstablishesAndRestoresPhase) {
  g_phase_during_routine = VpiToolPhase::kFull;
  g_routine_systf_registered = false;
  g_routine_allowed_cb_registered = false;
  g_routine_illegal_cb_registered = false;

  VlogStartupRoutine routines[] = {&StartupRoutine, nullptr};
  InvokeVlogStartupRoutines(routines);

  // The routine saw the startup phase in force.
  EXPECT_EQ(g_phase_during_routine, VpiToolPhase::kStartup);
  // The two available routines worked; the disallowed callback reason did not.
  EXPECT_TRUE(g_routine_systf_registered);
  EXPECT_TRUE(g_routine_allowed_cb_registered);
  EXPECT_FALSE(g_routine_illegal_cb_registered);
  // The phase is restored once the array has been walked.
  EXPECT_EQ(vpi_ctx_.ToolPhase(), VpiToolPhase::kFull);
}

}  // namespace
}  // namespace delta
