#include "simulator/sv_vpi_user.h"

#include <optional>

#include "simulator/vpi_assertion_cb.h"
#include "simulator/vpi_coverage.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_routine_error_scope.h"
#include "simulator/vpi_user.h"

vpiHandle vpi_register_assertion_cb(vpiHandle assertion, PLI_INT32 reason,
                                    vpi_assertion_callback_func* cb_rtn,
                                    PLI_BYTE8* user_data) {
  delta::VpiRoutineErrorScope error_scope;
  return delta::VpiHandleOf(delta::VpiRegisterAssertionCb(
      delta::VpiObjectOf(assertion), reason, cb_rtn, user_data));
}

namespace delta {

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
