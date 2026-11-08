#pragma once

namespace delta {

struct RtlirDesign;
class SimContext;
class Arena;

void CallBuildPeriodSystfRoutines(const RtlirDesign* design, SimContext& ctx,
                                  Arena& arena);

}  // namespace delta
