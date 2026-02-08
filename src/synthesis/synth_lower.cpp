#include "synthesis/synth_lower.h"

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaboration/rtlir.h"

namespace delta {

SynthLowering::SynthLowering(Arena& arena, DiagEngine& diag) : arena_(arena), diag_(diag) {}

AigGraph* SynthLowering::lower(const RtlirModule* module) {
    auto* graph = arena_.create<AigGraph>();

    if (!module) {
        return graph;
    }

    // TODO: Iterate over module ports and create primary inputs/outputs.
    // TODO: Lower continuous assignments.
    // TODO: Lower always_comb processes.
    // TODO: Lower always_ff processes to latches.

    for (const auto& assign : module->assigns) {
        lower_cont_assign(assign, *graph);
    }

    for (const auto& proc : module->processes) {
        if (proc.kind == ProcessKind::AlwaysComb) {
            lower_always_comb(proc, *graph);
        }
    }

    return graph;
}

void SynthLowering::lower_cont_assign(const RtlirContAssign& /*assign*/, AigGraph& /*graph*/) {
    // TODO: Walk the RHS expression tree and build AIG nodes.
    // Each bit of a multi-bit assignment produces a separate AIG output.
    // Expression opcodes map as follows:
    //   - bitwise AND  -> add_and
    //   - bitwise OR   -> add_or
    //   - bitwise XOR  -> add_xor
    //   - bitwise NOT  -> add_not
    //   - ternary ?:   -> add_mux
}

void SynthLowering::lower_always_comb(const RtlirProcess& /*proc*/, AigGraph& /*graph*/) {
    // TODO: Flatten the combinational process body into dataflow form,
    // then lower each resulting assignment as if it were a cont_assign.
    // Must handle if/case as MUX chains.
}

} // namespace delta
