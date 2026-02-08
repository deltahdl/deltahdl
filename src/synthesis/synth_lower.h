#pragma once

#include "synthesis/aig.h"

#include <cstdint>

namespace delta {

// Forward declarations.
class Arena;
class DiagEngine;
struct RtlirModule;
struct RtlirContAssign;
struct RtlirProcess;

// --- RTLIR-to-AIG lowering ---
//
// Translates elaborated RTLIR modules into an AIG representation suitable
// for technology-independent optimization passes.

class SynthLowering {
  public:
    SynthLowering(Arena& arena, DiagEngine& diag);

    /// Lower an RTLIR module to an And-Inverter Graph.
    /// Caller owns the returned graph (allocated via the arena).
    AigGraph* lower(const RtlirModule* module);

  private:
    /// Lower a continuous assignment into the current AIG.
    void lower_cont_assign(const RtlirContAssign& assign, AigGraph& graph);

    /// Lower a combinational always block into the current AIG.
    void lower_always_comb(const RtlirProcess& proc, AigGraph& graph);

    Arena& arena_;
    [[maybe_unused]] DiagEngine& diag_;
};

} // namespace delta
