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

// §36.10.1 (C2): the nonzero result genuinely distinguishes an error from
// success - when the previously called routine did not error, the same query
// returns zero, so a nonzero return is what signals an error occurred.
TEST_F(VpiErrorHandling, ChkErrorReturnsZeroWhenNoErrorOccurred) {
  CallVpiRoutineThatSucceeds();

  EXPECT_EQ(vpi_chk_error(nullptr), 0);
}

// §36.10.1 (C2, edge): the determination is scoped to the previously called
// VPI routine, not to any error ever seen. After a routine errors, a later
// routine that succeeds becomes the previously called one, so vpi_chk_error()
// reports no error - the pending status does not persist across a good call.
TEST_F(VpiErrorHandling, ChkErrorTracksMostRecentRoutineNotAnyPriorError) {
  CallVpiRoutineThatErrors();
  ASSERT_NE(vpi_chk_error(nullptr), 0);

  CallVpiRoutineThatSucceeds();

  EXPECT_EQ(vpi_chk_error(nullptr), 0);
}

// §36.10.1 (C4): the vpi_chk_error() routine can provide detailed information
// about the error through the structure passed to it.
TEST_F(VpiErrorHandling, ChkErrorProvidesDetailedInformation) {
  CallVpiRoutineThatErrors();

  SVpiErrorInfo info = {};
  int result = vpi_chk_error(&info);

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

// §36.10.1: "Callbacks can be set up for when an error occurs as well."
// Registering one is half of that sentence and the case above is that half.
// The other half is the occurrence, and no error a VPI routine recorded reached
// a callback at all: they could be set up, and then nothing ever happened to
// them.

// What the applications below recorded. A callback routine is a plain C
// function with no return path to the case that provoked it.
int g_pli_error_calls = 0;
int g_error_calls = 0;
int g_level_seen_in_callback = 0;

int CountingPliErrorCb(VpiCbData*) {
  ++g_pli_error_calls;
  // §38.36.3: "On a cbError callback, the routine vpi_chk_error() can be called
  // to retrieve error information." vpi_chk_error() is the one routine that
  // leaves the error status alone (§38.2), so the error is still standing when
  // the callback asks about it.
  g_level_seen_in_callback = vpi_chk_error(nullptr);
  return 0;
}

int CountingErrorCb(VpiCbData*) {
  ++g_error_calls;
  return 0;
}

void RegisterErrorCallbacks() {
  g_pli_error_calls = 0;
  g_error_calls = 0;
  g_level_seen_in_callback = 0;

  s_cb_data pli_err = {};
  pli_err.reason = cbPLIError;
  pli_err.cb_rtn = &CountingPliErrorCb;
  ASSERT_NE(vpi_register_cb(&pli_err), nullptr);

  s_cb_data err = {};
  err.reason = cbError;
  err.cb_rtn = &CountingErrorCb;
  ASSERT_NE(vpi_register_cb(&err), nullptr);
}

TEST_F(VpiErrorHandling, TheErrorCallbackOccursWhenTheErrorDoes) {
  RegisterErrorCallbacks();

  CallVpiRoutineThatErrors();

  // §38.36.3 separates the two reasons by where the error arose: cbPLIError is
  // a "simulation run-time error occurred in a PLI function call" and this one
  // arose inside vpi_register_systf(), which is one.
  EXPECT_EQ(g_pli_error_calls, 1);
  EXPECT_EQ(g_error_calls, 0);
  // And the callback could ask what the error was, which is §36.10.1's other
  // sentence: "the vpi_chk_error() routine can provide detailed information
  // about the error."
  EXPECT_EQ(g_level_seen_in_callback, vpiError);
}

TEST_F(VpiErrorHandling, NoCallbackOccursWhenTheRoutineSucceeds) {
  // The callback is set up for an error, so a routine that recorded none
  // delivers nothing. Without this the case above passes on a tool that ran the
  // error callbacks at the end of every VPI routine it was handed.
  RegisterErrorCallbacks();

  CallVpiRoutineThatSucceeds();

  EXPECT_EQ(g_pli_error_calls, 0);
  EXPECT_EQ(g_error_calls, 0);
}

// What the re-entrant application below recorded.
int g_nested_calls = 0;

int ReentrantPliErrorCb(VpiCbData*) {
  ++g_nested_calls;
  // A callback is free to call VPI routines of its own, and this one calls the
  // routine that records an error.
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = "still_no_dollar_prefix";
  vpi_register_systf(&data);
  return 0;
}

TEST_F(VpiErrorHandling, AnErrorRaisedInsideTheCallbackDoesNotReenterIt) {
  g_nested_calls = 0;

  s_cb_data pli_err = {};
  pli_err.reason = cbPLIError;
  pli_err.cb_rtn = &ReentrantPliErrorCb;
  ASSERT_NE(vpi_register_cb(&pli_err), nullptr);

  CallVpiRoutineThatErrors();

  // §36.10.1 says nothing about a callback's own errors, and the one thing a
  // tool must not do with them is hand this callback an error it has not
  // returned from yet. It runs once for the error that occurred, and the error
  // its own routine call recorded is left standing for whoever asks next.
  EXPECT_EQ(g_nested_calls, 1);
}

}  // namespace
}  // namespace delta
