#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

int ErrorCb(VpiCbData*) { return 0; }

class VpiErrorHandling : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // §36.10.1: drive the previously called VPI routine into its error path so
  // an error status is left pending. vpi_register_systf() rejects a name that
  // lacks the leading dollar sign, which records an error (see §38.37.1).
  void CallVpiRoutineThatErrors() {
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = "no_dollar_prefix";
    vpi_register_systf(&data);
  }

  // §36.10.1: a previous VPI routine call that completes without error.
  void CallVpiRoutineThatSucceeds() {
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = "$ok";
    vpi_register_systf(&data);
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

// §36.10.1 (C1/C2): vpi_chk_error() is the routine provided to determine
// whether an error occurred; it returns a nonzero value when the previously
// called VPI routine resulted in an error.
TEST_F(VpiErrorHandling, ChkErrorReturnsNonzeroWhenErrorOccurred) {
  CallVpiRoutineThatErrors();

  EXPECT_NE(VpiChkErrorC(nullptr), 0);
}

// §36.10.1 (C2): the nonzero result genuinely distinguishes an error from
// success - when the previously called routine did not error, the same query
// returns zero, so a nonzero return is what signals an error occurred.
TEST_F(VpiErrorHandling, ChkErrorReturnsZeroWhenNoErrorOccurred) {
  CallVpiRoutineThatSucceeds();

  EXPECT_EQ(VpiChkErrorC(nullptr), 0);
}

// §36.10.1 (C2, edge): the determination is scoped to the previously called
// VPI routine, not to any error ever seen. After a routine errors, a later
// routine that succeeds becomes the previously called one, so vpi_chk_error()
// reports no error - the pending status does not persist across a good call.
TEST_F(VpiErrorHandling, ChkErrorTracksMostRecentRoutineNotAnyPriorError) {
  CallVpiRoutineThatErrors();
  ASSERT_NE(VpiChkErrorC(nullptr), 0);

  CallVpiRoutineThatSucceeds();

  EXPECT_EQ(VpiChkErrorC(nullptr), 0);
}

// §36.10.1 (C4): the vpi_chk_error() routine can provide detailed information
// about the error through the structure passed to it.
TEST_F(VpiErrorHandling, ChkErrorProvidesDetailedInformation) {
  CallVpiRoutineThatErrors();

  SVpiErrorInfo info = {};
  int result = VpiChkErrorC(&info);

  EXPECT_NE(result, 0);
  EXPECT_NE(info.level, 0);
  EXPECT_NE(info.message, nullptr);
}

// §36.10.1 (C3): callbacks can be set up for when an error occurs - a callback
// registered for the error reasons is accepted and yields a usable handle.
TEST_F(VpiErrorHandling, ErrorCallbackCanBeRegistered) {
  s_cb_data err = {};
  err.reason = cbError;
  err.cb_rtn = ErrorCb;
  EXPECT_NE(vpi_register_cb(&err), nullptr);

  s_cb_data pli_err = {};
  pli_err.reason = cbPLIError;
  pli_err.cb_rtn = ErrorCb;
  EXPECT_NE(vpi_register_cb(&pli_err), nullptr);
}

}  // namespace
}  // namespace delta
