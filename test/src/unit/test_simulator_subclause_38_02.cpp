#include <gtest/gtest.h>

#include "helpers_vpi_error_fixture.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

// The compile-based variants, declared as vpi_compatibility.cpp defines them,
// with the C linkage Annex K.2 gives the prototypes Annex L.2 renames to these,
// so one translation unit can call them alongside the plain routines.
extern "C" {
PLI_INT32 vpi_get_1364v1995(PLI_INT32 property, vpiHandle obj);
PLI_INT32 vpi_control_1800v2012(PLI_INT32 operation, ...);
vpiHandle vpi_iterate_1364v2005(PLI_INT32 type, vpiHandle ref);
}

namespace delta {
namespace {

using VpiErrorCheckSim = VpiErrorRaisingFixture;

// §38.2 (R2): with no preceding error, vpi_chk_error() returns 0 (false) and
// leaves the supplied structure's severity level at zero.
TEST_F(VpiErrorCheckSim, ChkErrorNoErrorReturnsZero) {
  s_vpi_error_info info = {};
  int result = vpi_chk_error(&info);
  EXPECT_EQ(result, 0);
  EXPECT_EQ(info.level, 0);
}

// §38.2: a null error_info_p is accepted - the detail is simply not copied out.
TEST_F(VpiErrorCheckSim, ChkErrorNullDoesNotCrash) {
  int result = vpi_chk_error(nullptr);

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

  s_vpi_error_info info = {};
  int result = vpi_chk_error(&info);

  EXPECT_EQ(result, vpiError);
  EXPECT_EQ(info.level, vpiError);
  EXPECT_NE(info.message, nullptr);
}

// §38.2 (E1): the error status is reset by any VPI routine call except
// vpi_chk_error(). A successful routine call after an error clears it, so a
// subsequent vpi_chk_error() reports 0.
TEST_F(VpiErrorCheckSim, OtherRoutineCallResetsErrorStatus) {
  RaiseError();
  ASSERT_EQ(vpi_chk_error(nullptr), vpiError);

  // A different, successful VPI routine call resets the pending error status.
  s_vpi_vlog_info vlog = {};
  vpi_get_vlog_info(&vlog);

  EXPECT_EQ(vpi_chk_error(nullptr), 0);
}

// §38.2 (E1, edge): the reset is performed on entry to any VPI routine, not
// just one. A successful call to the very routine that previously failed - here
// vpi_register_systf() with a well-formed name - still clears the prior error,
// confirming the reset is a general per-routine behavior.
TEST_F(VpiErrorCheckSim, SuccessfulRoutineCallClearsPriorError) {
  RaiseError();
  ASSERT_EQ(vpi_chk_error(nullptr), vpiError);

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname =
      VpiText("$ok");  // valid name: registration succeeds, records no error
  vpi_register_systf(&data);

  EXPECT_EQ(vpi_chk_error(nullptr), 0);
}

// §38.2 (E2): calling vpi_chk_error() has no effect on the error status, so two
// consecutive queries report the same pending severity level.
TEST_F(VpiErrorCheckSim, ChkErrorDoesNotResetErrorStatus) {
  RaiseError();

  EXPECT_EQ(vpi_chk_error(nullptr), vpiError);
  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(info.level, vpiError);
}

// §38.2 (Figure 38-1): the s_vpi_error_info structure carries a state beside
// the level, "vpi[Compile,PLI,Run]", and what it names is what the tool was
// doing when the error arose rather than how severe the error was. That is the
// level's job, and the two fields are numbered independently: an error the
// registration routine refused a name with had its state set to the level's own
// constant, which reads as vpiRun -- the tool executing the simulation -- for
// an error raised inside a VPI routine before the simulation started.
TEST_F(VpiErrorCheckSim, TheStateNamesTheActivityAndTheLevelTheSeverity) {
  RaiseError();

  s_vpi_error_info info = {};
  ASSERT_EQ(vpi_chk_error(&info), vpiError);

  // The routine itself is what raised this, so the activity is the PLI.
  EXPECT_EQ(info.state, vpiPLI);
  EXPECT_EQ(info.level, vpiError);
  // And the two fields do not carry one value between them.
  EXPECT_NE(info.state, info.level);
}

// §38.2: the state does not move with the severity. A routine that records a
// warning rather than an error was doing the same thing when it did so, so the
// state reads the same and only the level differs. vpi_free_object() is the
// warning to hand: Annex C.2.4 deprecated it, and the call records that.
TEST_F(VpiErrorCheckSim, TheStateIsTheSameWhateverTheSeverity) {
  vpi_free_object(nullptr);

  s_vpi_error_info info = {};
  ASSERT_EQ(vpi_chk_error(&info), vpiWarning);

  EXPECT_EQ(info.state, vpiPLI);
  EXPECT_EQ(info.level, vpiWarning);
}

// §38.2 (Figure 38-1): the three states the field is drawn from. They are their
// own set of constants, listed in Annex K beside the severity levels rather
// than among them, and the overlap in value with vpiNotice, vpiWarning and
// vpiError is what makes a state written with a level's constant invisible.
TEST_F(VpiErrorCheckSim, TheStateConstantsAreTheThreeTheFigureNames) {
  EXPECT_EQ(vpiCompile, 1);
  EXPECT_EQ(vpiPLI, 2);
  EXPECT_EQ(vpiRun, 3);
}

// §38.2 with §36.12.2.1: the names a compatibility mode gives the routines are
// VPI routines too, so a successful call under one of them resets the error
// status as the plain routine's does (#7445).
TEST_F(VpiErrorCheckSim, ACompatibilityModeRoutineResetsErrorStatus) {
  VpiObject net;
  net.type = vpiNet;
  RaiseError();
  EXPECT_EQ(vpi_get_1364v1995(vpiType, VpiHandleOf(&net)), vpiNet);
  EXPECT_EQ(vpi_chk_error(nullptr), 0);
  RaiseError();
  EXPECT_EQ(vpi_control_1800v2012(vpiSetInteractiveScope, VpiHandleOf(&net)),
            1);
  EXPECT_EQ(vpi_chk_error(nullptr), 0);
  RaiseError();
  vpi_iterate_1364v2005(vpiModule, nullptr);
  EXPECT_EQ(vpi_chk_error(nullptr), 0);
}

// §38.2 with §39.4.2: vpi_register_assertion_cb() is a VPI routine, so it
// resets the error status, and a placement that only answers NULL for want of
// an assertion records no error of its own (#7447).
TEST_F(VpiErrorCheckSim, RegisteringAnAssertionCallbackResetsErrorStatus) {
  RaiseError();
  ASSERT_EQ(vpi_chk_error(nullptr), vpiError);
  EXPECT_EQ(
      vpi_register_assertion_cb(nullptr, cbAssertionStart, nullptr, nullptr),
      nullptr);
  EXPECT_EQ(vpi_chk_error(nullptr), 0);
}

}  // namespace
}  // namespace delta
