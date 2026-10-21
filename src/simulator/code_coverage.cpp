#include "simulator/code_coverage.h"

#include <string>

#include "simulator/assertion_coverage.h"
#include "simulator/fsm_coverage.h"
#include "simulator/statement_coverage.h"
#include "simulator/toggle_coverage.h"

namespace delta {

std::string CoverageInstancePrefix(std::string prefix) {
  if (!prefix.empty() && prefix.back() == '.') prefix.pop_back();
  return prefix;
}

void AttachCodeCoverage(const RtlirDesign* design, SimContext& ctx) {
  AttachStatementCoverage(design, ctx);
  AttachToggleCoverage(design, ctx);
  AttachAssertionCoverage(design, ctx);
  AttachFsmCoverage(design, ctx);
}

}  // namespace delta
