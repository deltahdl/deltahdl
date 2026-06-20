#include <gtest/gtest.h>

#include <set>

#include "simulator/sv_vpi_user.h"

// Clause 40.5.1 enumerates the symbolic names that extend the VPI enumerations
// for coverage. Each name must be defined by the VPI header as a distinct
// enumeration constant. Referencing each symbol below forces it to be defined
// in production (an undefined name fails to compile), and asserting the set
// holds all 23 values observes that production carries them as a proper
// enumeration with no collisions.

namespace {

TEST(SvVpiUserCoverageEnums, AllExtensionsDistinct) {
  const std::set<int> kValues = {
      // Coverage control.
      vpiCoverageStart,
      vpiCoverageStop,
      vpiCoverageReset,
      vpiCoverageCheck,
      vpiCoverageMerge,
      vpiCoverageSave,
      // Coverage type properties.
      vpiAssertCoverage,
      vpiFsmStateCoverage,
      vpiStatementCoverage,
      vpiToggleCoverage,
      // Coverage status properties.
      vpiCovered,
      vpiCoveredMax,
      vpiCoveredCount,
      // Assertion-specific coverage status properties.
      vpiAssertAttemptCovered,
      vpiAssertSuccessCovered,
      vpiAssertFailureCovered,
      vpiAssertVacuousSuccessCovered,
      vpiAssertDisableCovered,
      vpiAssertKillCovered,
      // FSM-specific methods.
      vpiFsmStates,
      vpiFsmStateExpression,
      // FSM handle types (vpi types).
      vpiFsm,
      vpiFsmHandle,
  };
  EXPECT_EQ(kValues.size(), 23u);
}

}  // namespace
