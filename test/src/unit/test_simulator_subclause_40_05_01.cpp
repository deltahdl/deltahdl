#include <gtest/gtest.h>

#include <set>

#include "simulator/sv_vpi_user.h"

namespace {

TEST(SvVpiUserCoverageEnums, AllExtensionsDistinct) {
  const std::set<int> kValues = {
      vpiCoverageStart,
      vpiCoverageStop,
      vpiCoverageReset,
      vpiCoverageCheck,
      vpiCoverageMerge,
      vpiCoverageSave,
      vpiAssertCoverage,
      vpiFsmStateCoverage,
      vpiStatementCoverage,
      vpiToggleCoverage,
      vpiCovered,
      vpiCoveredMax,
      vpiCoveredCount,
      vpiAssertAttemptCovered,
      vpiAssertSuccessCovered,
      vpiAssertFailureCovered,
      vpiAssertVacuousSuccessCovered,
      vpiAssertDisableCovered,
      vpiAssertKillCovered,
      vpiFsmStates,
      vpiFsmStateExpression,
      vpiFsm,
      vpiFsmHandle,
  };
  EXPECT_EQ(kValues.size(), 23u);
}

}  // namespace
