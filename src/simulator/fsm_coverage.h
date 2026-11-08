#pragma once

#include "simulator/vpi_coverage.h"

namespace delta {

class CoverageControlState;
class SimContext;
struct FsmHandleRef;
struct RtlirDesign;

void AttachFsmCoverage(const RtlirDesign* design, SimContext& ctx);

EntityCoverage FsmHandleCoverage(const FsmHandleRef& handle,
                                 CoverageControlState& cov);

}  // namespace delta
