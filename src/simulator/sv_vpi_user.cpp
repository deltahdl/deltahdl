

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
std::optional<CoverageProperty> CoveragePropertyFromVpi(int property) {
  switch (property) {
    case vpiAssertCoverage:
      return CoverageProperty::kAssertCoverage;
    case vpiFsmStateCoverage:
      return CoverageProperty::kFsmStateCoverage;
    case vpiStatementCoverage:
      return CoverageProperty::kStatementCoverage;
    case vpiToggleCoverage:
      return CoverageProperty::kToggleCoverage;
    case vpiCovered:
      return CoverageProperty::kCovered;
    case vpiCoveredCount:
      return CoverageProperty::kCoveredCount;
    case vpiAssertAttemptCovered:
      return CoverageProperty::kAssertAttemptCovered;
    case vpiAssertSuccessCovered:
      return CoverageProperty::kAssertSuccessCovered;
    case vpiAssertFailureCovered:
      return CoverageProperty::kAssertFailureCovered;
    case vpiAssertVacuousSuccessCovered:
      return CoverageProperty::kAssertVacuousSuccessCovered;
    case vpiAssertDisableCovered:
      return CoverageProperty::kAssertDisableCovered;
    case vpiAssertKillCovered:
      return CoverageProperty::kAssertKillCovered;
    default:
      return std::nullopt;
  }
}

}  // namespace delta
