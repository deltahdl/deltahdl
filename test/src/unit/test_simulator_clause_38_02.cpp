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

class VpiErrorCheckSim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // §38.2: drive a VPI routine into its error path so an error status is
  // pending. vpi_register_systf() rejects a name that does not begin with a
  // dollar sign and records a vpiError-level error (see §36.9.1 / §38.37.1).
  void RaiseError() {
    s_vpi_systf_data data = {};
    data.type = vpiSysTask;
    data.tfname = "missing_dollar";
    vpi_register_systf(&data);
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

// §38.2 (R2): with no preceding error, vpi_chk_error() returns 0 (false) and
// leaves the supplied structure's severity level at zero.
TEST_F(VpiErrorCheckSim, ChkErrorNoErrorReturnsZero) {
  SVpiErrorInfo info = {};
  int result = VpiChkErrorC(&info);
  EXPECT_EQ(result, 0);
  EXPECT_EQ(info.level, 0);
}

// §38.2: a null error_info_p is accepted - the detail is simply not copied out.
TEST_F(VpiErrorCheckSim, ChkErrorNullDoesNotCrash) {
  int result = VpiChkErrorC(nullptr);

  EXPECT_EQ(result, 0);
}

// §38.2 Table 38-1 (T1): the five severity constants run from lowest
// (vpiNotice) to highest (vpiInternal), with strictly increasing, distinct
// values so vpiSystem outranks vpiError and vpiInternal outranks them all.
TEST_F(VpiErrorCheckSim, SeverityConstantsAreOrderedLowestToHighest) {
  EXPECT_EQ(vpiNotice, 1);
  EXPECT_EQ(vpiWarning, 2);
  EXPECT_EQ(vpiError, 3);
  EXPECT_EQ(vpiSystem, 4);
  EXPECT_EQ(vpiInternal, 5);
  EXPECT_LT(vpiNotice, vpiWarning);
  EXPECT_LT(vpiWarning, vpiError);
  EXPECT_LT(vpiError, vpiSystem);
  EXPECT_LT(vpiSystem, vpiInternal);
}

// §38.2 (R1, F1): after a VPI routine fails, vpi_chk_error() returns the
// error's severity-level constant (not a plain boolean) and fills in the
// s_vpi_error_info structure describing the error.
TEST_F(VpiErrorCheckSim, ChkErrorReturnsSeverityLevelAfterError) {
  RaiseError();

  SVpiErrorInfo info = {};
  int result = VpiChkErrorC(&info);

  EXPECT_EQ(result, vpiError);
  EXPECT_EQ(info.level, vpiError);
  EXPECT_NE(info.message, nullptr);
}

// §38.2 (E1): the error status is reset by any VPI routine call except
// vpi_chk_error(). A successful routine call after an error clears it, so a
// subsequent vpi_chk_error() reports 0.
TEST_F(VpiErrorCheckSim, OtherRoutineCallResetsErrorStatus) {
  RaiseError();
  ASSERT_EQ(VpiChkErrorC(nullptr), vpiError);

  // A different, successful VPI routine call resets the pending error status.
  SVpiVlogInfo vlog = {};
  vpi_get_vlog_info(&vlog);

  EXPECT_EQ(VpiChkErrorC(nullptr), 0);
}

// §38.2 (E1, edge): the reset is performed on entry to any VPI routine, not
// just one. A successful call to the very routine that previously failed - here
// vpi_register_systf() with a well-formed name - still clears the prior error,
// confirming the reset is a general per-routine behavior.
TEST_F(VpiErrorCheckSim, SuccessfulRoutineCallClearsPriorError) {
  RaiseError();
  ASSERT_EQ(VpiChkErrorC(nullptr), vpiError);

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = "$ok";  // valid name: registration succeeds, records no error
  vpi_register_systf(&data);

  EXPECT_EQ(VpiChkErrorC(nullptr), 0);
}

// §38.2 (E2): calling vpi_chk_error() has no effect on the error status, so two
// consecutive queries report the same pending severity level.
TEST_F(VpiErrorCheckSim, ChkErrorDoesNotResetErrorStatus) {
  RaiseError();

  EXPECT_EQ(VpiChkErrorC(nullptr), vpiError);
  SVpiErrorInfo info = {};
  EXPECT_EQ(VpiChkErrorC(&info), vpiError);
  EXPECT_EQ(info.level, vpiError);
}

}  // namespace
}  // namespace delta
