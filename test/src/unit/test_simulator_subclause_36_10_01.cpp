#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

int ErrorCb(s_cb_data*) { return 0; }

class VpiErrorHandling : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  void CallVpiRoutineThatErrors() {
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("no_dollar_prefix");
    vpi_register_systf(&data);
  }

  void CallVpiRoutineThatSucceeds() {
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = VpiText("$ok");
    vpi_register_systf(&data);
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

TEST_F(VpiErrorHandling, ChkErrorReturnsZeroWhenNoErrorOccurred) {
  CallVpiRoutineThatSucceeds();

  EXPECT_EQ(vpi_chk_error(nullptr), 0);
}

TEST_F(VpiErrorHandling, ChkErrorTracksMostRecentRoutineNotAnyPriorError) {
  CallVpiRoutineThatErrors();
  ASSERT_NE(vpi_chk_error(nullptr), 0);

  CallVpiRoutineThatSucceeds();

  EXPECT_EQ(vpi_chk_error(nullptr), 0);
}

TEST_F(VpiErrorHandling, ChkErrorProvidesDetailedInformation) {
  CallVpiRoutineThatErrors();

  s_vpi_error_info info = {};
  int result = vpi_chk_error(&info);

  EXPECT_NE(result, 0);
  EXPECT_NE(info.level, 0);
  EXPECT_NE(info.message, nullptr);
}

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

int g_pli_error_calls = 0;
int g_error_calls = 0;
int g_level_seen_in_callback = 0;

int CountingPliErrorCb(s_cb_data*) {
  ++g_pli_error_calls;
  g_level_seen_in_callback = vpi_chk_error(nullptr);
  return 0;
}

int CountingErrorCb(s_cb_data*) {
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

  EXPECT_EQ(g_pli_error_calls, 1);
  EXPECT_EQ(g_error_calls, 0);
  EXPECT_EQ(g_level_seen_in_callback, vpiError);
}

TEST_F(VpiErrorHandling, NoCallbackOccursWhenTheRoutineSucceeds) {
  RegisterErrorCallbacks();

  CallVpiRoutineThatSucceeds();

  EXPECT_EQ(g_pli_error_calls, 0);
  EXPECT_EQ(g_error_calls, 0);
}

int g_nested_calls = 0;

int ReentrantPliErrorCb(s_cb_data*) {
  ++g_nested_calls;
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("still_no_dollar_prefix");
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

  EXPECT_EQ(g_nested_calls, 1);
}

}  // namespace
}  // namespace delta
