#pragma once

// IEEE 1800-2023 §40.2.2 toggle coverage: whether each bit of every signal,
// wire and register, has held both a 0 and a 1, and, as §40.2.2 lets an
// implementation offer and §40.5.2's vpiCoveredCount reads, how many times
// each has toggled.

#include <string>

#include "simulator/vpi_coverage.h"

namespace delta {

class CoverageControlState;
class SimContext;
struct RtlirDesign;
struct Variable;

// §40.2.2: count the bits of every instance's ports, nets and variables as
// its coverable toggle items, and watch them. A real, a string, an event, a
// class handle, a virtual interface and an unpacked aggregate hold no bits
// that toggle between 0 and 1 and are left out.
void AttachToggleCoverage(const RtlirDesign* design, SimContext& ctx);

// §40.5.2: the bits of the signal `var` of the instance `scope`: how many
// there are, how many have held both values, and their toggles summed.
EntityCoverage SignalToggleCoverage(const Variable* var,
                                    const std::string& scope,
                                    CoverageControlState& cov);

}  // namespace delta
