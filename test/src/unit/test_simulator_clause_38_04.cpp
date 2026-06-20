#include <gtest/gtest.h>

#include <cstring>
#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiSimControlSim : public ::testing::Test {
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

// §38.4: vpiFinish requests $finish on return of the application routine and
// carries the diagnostic message level that task reports; vpi_control() returns
// 1 on success and forwards the level through to the pending built-in.
TEST_F(VpiSimControlSim, ControlFinishCarriesDiagLevel) {
  EXPECT_FALSE(vpi_ctx_.FinishRequested());
  int result = VpiControlC(vpiFinish, 2);
  EXPECT_EQ(result, 1);
  EXPECT_TRUE(vpi_ctx_.FinishRequested());
  EXPECT_EQ(vpi_ctx_.FinishDiagLevel(), 2);
}

// §38.4: vpiStop likewise requests $stop and carries its diagnostic message
// level.
TEST_F(VpiSimControlSim, ControlStopCarriesDiagLevel) {
  EXPECT_FALSE(vpi_ctx_.StopRequested());
  int result = VpiControlC(vpiStop, 1);
  EXPECT_EQ(result, 1);
  EXPECT_TRUE(vpi_ctx_.StopRequested());
  EXPECT_EQ(vpi_ctx_.StopDiagLevel(), 1);
}

// §38.4: vpiReset requests the $reset built-in and is passed three additional
// integer arguments (stop_value, reset_value, diagnostics_value).
TEST_F(VpiSimControlSim, ControlResetCarriesThreeArguments) {
  EXPECT_FALSE(vpi_ctx_.ResetRequested());
  int result = VpiControlC(vpiReset, 4, 5, 6);
  EXPECT_EQ(result, 1);
  EXPECT_TRUE(vpi_ctx_.ResetRequested());
  EXPECT_EQ(vpi_ctx_.ResetStopValue(), 4);
  EXPECT_EQ(vpi_ctx_.ResetResetValue(), 5);
  EXPECT_EQ(vpi_ctx_.ResetDiagValue(), 6);
}

// §38.4: vpiSetInteractiveScope immediately switches the tool's interactive
// scope to the supplied vpiScope handle.
TEST_F(VpiSimControlSim, ControlSetInteractiveScope) {
  EXPECT_EQ(vpi_ctx_.InteractiveScope(), nullptr);
  VpiHandle scope = vpi_ctx_.CreateModule("top", "top");
  int result = VpiControlC(vpiSetInteractiveScope, scope);
  EXPECT_EQ(result, 1);
  EXPECT_EQ(vpi_ctx_.InteractiveScope(), scope);
}

// §38.4: vpiSetInteractiveScope retargets to a *new* scope each time it is
// invoked, so a later call replaces the scope an earlier call established
// rather than being ignored once a scope is set.
TEST_F(VpiSimControlSim, ControlSetInteractiveScopeReplacesPriorScope) {
  VpiHandle first = vpi_ctx_.CreateModule("top", "top");
  EXPECT_EQ(VpiControlC(vpiSetInteractiveScope, first), 1);
  EXPECT_EQ(vpi_ctx_.InteractiveScope(), first);

  VpiHandle second = vpi_ctx_.CreateModule("sub", "top.sub");
  EXPECT_EQ(VpiControlC(vpiSetInteractiveScope, second), 1);
  EXPECT_EQ(vpi_ctx_.InteractiveScope(), second);
}

// §38.4: vpiReset is signalled by the request itself, not by the magnitude of
// its arguments. Passing zero for all three values still requests the reset and
// records those zeros.
TEST_F(VpiSimControlSim, ControlResetWithZeroArgumentsStillRequestsReset) {
  EXPECT_FALSE(vpi_ctx_.ResetRequested());
  int result = VpiControlC(vpiReset, 0, 0, 0);
  EXPECT_EQ(result, 1);
  EXPECT_TRUE(vpi_ctx_.ResetRequested());
  EXPECT_EQ(vpi_ctx_.ResetStopValue(), 0);
  EXPECT_EQ(vpi_ctx_.ResetResetValue(), 0);
  EXPECT_EQ(vpi_ctx_.ResetDiagValue(), 0);
}

// §38.4: an operation vpi_control() does not recognize fails (returns 0) and
// must do nothing else — no stop, finish, or reset is requested and the
// interactive scope is left as it was.
TEST_F(VpiSimControlSim, ControlUnknownOpIsInert) {
  int result = VpiControlC(12345, 0);
  EXPECT_EQ(result, 0);
  EXPECT_FALSE(vpi_ctx_.StopRequested());
  EXPECT_FALSE(vpi_ctx_.FinishRequested());
  EXPECT_FALSE(vpi_ctx_.ResetRequested());
  EXPECT_EQ(vpi_ctx_.InteractiveScope(), nullptr);
}

}  // namespace
}  // namespace delta
