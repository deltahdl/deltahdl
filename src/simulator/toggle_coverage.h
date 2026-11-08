#pragma once

#include <string>

#include "simulator/vpi_coverage.h"

namespace delta {

class CoverageControlState;
class SimContext;
struct RtlirDesign;
struct Variable;

void AttachToggleCoverage(const RtlirDesign* design, SimContext& ctx);

EntityCoverage SignalToggleCoverage(const Variable* var,
                                    const std::string& scope,
                                    CoverageControlState& cov);

}  // namespace delta
