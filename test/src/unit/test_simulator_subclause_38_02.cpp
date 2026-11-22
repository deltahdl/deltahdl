#include <gtest/gtest.h>

#include <string>

#include "helpers_vpi_error_fixture.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

extern "C" {
PLI_INT32 vpi_get_1364v1995(PLI_INT32 property, vpiHandle obj);
PLI_INT32 vpi_control_1800v2012(PLI_INT32 operation, ...);
vpiHandle vpi_iterate_1364v2005(PLI_INT32 type, vpiHandle ref);
}

namespace delta {
namespace {

using VpiErrorCheckSim = VpiErrorRaisingFixture;

TEST_F(VpiErrorCheckSim, ChkErrorNoErrorReturnsZero) {
  s_vpi_error_info info = {};
  int result = vpi_chk_error(&info);
  EXPECT_EQ(result, 0);
  EXPECT_EQ(info.level, 0);
}

TEST_F(VpiErrorCheckSim, ChkErrorNullDoesNotCrash) {
  int result = vpi_chk_error(nullptr);

  EXPECT_EQ(result, 0);
}

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

TEST_F(VpiErrorCheckSim, ChkErrorReturnsSeverityLevelAfterError) {
  RaiseError();

  s_vpi_error_info info = {};
  int result = vpi_chk_error(&info);

  EXPECT_EQ(result, vpiError);
  EXPECT_EQ(info.level, vpiError);
  EXPECT_NE(info.message, nullptr);
}

TEST_F(VpiErrorCheckSim, OtherRoutineCallResetsErrorStatus) {
  RaiseError();
  ASSERT_EQ(vpi_chk_error(nullptr), vpiError);

  s_vpi_vlog_info vlog = {};
  vpi_get_vlog_info(&vlog);

  EXPECT_EQ(vpi_chk_error(nullptr), 0);
}

TEST_F(VpiErrorCheckSim, SuccessfulRoutineCallClearsPriorError) {
  RaiseError();
  ASSERT_EQ(vpi_chk_error(nullptr), vpiError);

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$ok");
  vpi_register_systf(&data);

  EXPECT_EQ(vpi_chk_error(nullptr), 0);
}

TEST_F(VpiErrorCheckSim, ChkErrorDoesNotResetErrorStatus) {
  RaiseError();

  EXPECT_EQ(vpi_chk_error(nullptr), vpiError);
  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(info.level, vpiError);
}

TEST_F(VpiErrorCheckSim, TheStateNamesTheActivityAndTheLevelTheSeverity) {
  RaiseError();

  s_vpi_error_info info = {};
  ASSERT_EQ(vpi_chk_error(&info), vpiError);

  EXPECT_EQ(info.state, vpiPLI);
  EXPECT_EQ(info.level, vpiError);
  EXPECT_NE(info.state, info.level);
}

TEST_F(VpiErrorCheckSim, TheStateIsTheSameWhateverTheSeverity) {
  vpi_free_object(nullptr);

  s_vpi_error_info info = {};
  ASSERT_EQ(vpi_chk_error(&info), vpiWarning);

  EXPECT_EQ(info.state, vpiPLI);
  EXPECT_EQ(info.level, vpiWarning);
}

TEST_F(VpiErrorCheckSim, TheStateConstantsAreTheThreeTheFigureNames) {
  EXPECT_EQ(vpiCompile, 1);
  EXPECT_EQ(vpiPLI, 2);
  EXPECT_EQ(vpiRun, 3);
}

TEST_F(VpiErrorCheckSim, ACompatibilityModeRoutineResetsErrorStatus) {
  VpiObject net;
  net.type = vpiNet;
  RaiseError();
  EXPECT_EQ(vpi_get_1364v1995(vpiType, VpiHandleOf(&net)), vpiNet);
  EXPECT_EQ(vpi_chk_error(nullptr), 0);
  VpiObject scope;
  scope.type = vpiModule;
  RaiseError();
  EXPECT_EQ(vpi_control_1800v2012(vpiSetInteractiveScope, VpiHandleOf(&scope)),
            1);
  EXPECT_EQ(vpi_chk_error(nullptr), 0);
  RaiseError();
  vpi_iterate_1364v2005(vpiModule, nullptr);
  EXPECT_EQ(vpi_chk_error(nullptr), 0);
}

TEST_F(VpiErrorCheckSim, RegisteringAnAssertionCallbackResetsErrorStatus) {
  RaiseError();
  ASSERT_EQ(vpi_chk_error(nullptr), vpiError);
  EXPECT_EQ(
      vpi_register_assertion_cb(nullptr, cbAssertionStart, nullptr, nullptr),
      nullptr);
  EXPECT_EQ(vpi_chk_error(nullptr), 0);
}

TEST_F(VpiErrorCheckSim, RepeatedChecksWithNothingPendingBothReturnZero) {
  RaiseError();
  ASSERT_EQ(vpi_chk_error(nullptr), vpiError);
  s_vpi_vlog_info vlog = {};
  ASSERT_EQ(vpi_get_vlog_info(&vlog), 1);

  EXPECT_EQ(vpi_chk_error(nullptr), 0);
  s_vpi_error_info info = {};
  info.level = vpiInternal;
  EXPECT_EQ(vpi_chk_error(&info), 0);
  EXPECT_EQ(vpi_chk_error(nullptr), 0);
}

TEST_F(VpiErrorCheckSim, AnErrorAfterAWarningIsReportedAlone) {
  vpi_free_object(nullptr);
  ASSERT_EQ(vpi_chk_error(nullptr), vpiWarning);
  RaiseError();

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(info.level, vpiError);
}

TEST_F(VpiErrorCheckSim, AWarningAfterAnErrorIsReportedAlone) {
  RaiseError();
  ASSERT_EQ(vpi_chk_error(nullptr), vpiError);
  vpi_free_object(nullptr);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiWarning);
  EXPECT_EQ(info.level, vpiWarning);
}

TEST_F(VpiErrorCheckSim, DISABLED_TheErrorNamesTheProductAndCarriesACode) {
  s_vpi_vlog_info vlog = {};
  ASSERT_EQ(vpi_get_vlog_info(&vlog), 1);
  ASSERT_NE(vlog.product, nullptr);
  const std::string kProduct = vlog.product;

  for (int expected : {vpiError, vpiWarning}) {
    if (expected == vpiError) {
      RaiseError();
    } else {
      vpi_free_object(nullptr);
    }
    s_vpi_error_info info = {};
    ASSERT_EQ(vpi_chk_error(&info), expected);
    ASSERT_NE(info.product, nullptr) << expected;
    EXPECT_EQ(std::string(info.product), kProduct) << expected;
    ASSERT_NE(info.code, nullptr) << expected;
    EXPECT_STRNE(info.code, "") << expected;
  }
}

}  // namespace
}  // namespace delta
