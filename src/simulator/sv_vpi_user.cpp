

#include "simulator/sv_vpi_user.h"

#include "simulator/vpi_coverage.h"

vpiHandle vpi_register_assertion_cb(vpiHandle assertion, PLI_INT32 reason,
                                    vpi_assertion_callback_func cb_rtn,
                                    PLI_BYTE8* user_data) {
  (void)assertion;
  (void)reason;
  (void)cb_rtn;
  (void)user_data;
  return nullptr;
}

namespace delta {

// Maps a coverage property identifier from sv_vpi_user.h to the abstract
// CoverageProperty used by the §40.5.2 query helpers. Returns nullopt for an
// identifier that is not a coverage property.
std::optional<CoverageProperty> coverage_property_from_vpi(int property) {
  switch (property) {
    case vpiAssertCoverage:
      return CoverageProperty::AssertCoverage;
    case vpiFsmStateCoverage:
      return CoverageProperty::FsmStateCoverage;
    case vpiStatementCoverage:
      return CoverageProperty::StatementCoverage;
    case vpiToggleCoverage:
      return CoverageProperty::ToggleCoverage;
    case vpiCovered:
      return CoverageProperty::Covered;
    case vpiCoveredCount:
      return CoverageProperty::CoveredCount;
    case vpiAssertAttemptCovered:
      return CoverageProperty::AssertAttemptCovered;
    case vpiAssertSuccessCovered:
      return CoverageProperty::AssertSuccessCovered;
    case vpiAssertFailureCovered:
      return CoverageProperty::AssertFailureCovered;
    case vpiAssertVacuousSuccessCovered:
      return CoverageProperty::AssertVacuousSuccessCovered;
    case vpiAssertDisableCovered:
      return CoverageProperty::AssertDisableCovered;
    case vpiAssertKillCovered:
      return CoverageProperty::AssertKillCovered;
    default:
      return std::nullopt;
  }
}

}  // namespace delta
