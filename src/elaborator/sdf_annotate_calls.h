#pragma once

#include <string_view>

#include "common/source_loc.h"

namespace delta {

class DiagEngine;
struct RtlirDesign;

// §32.9: whether a procedure or a subroutine of a module of `design` calls
// $sdf_annotate, which is how an interconnect delay reaches a run that the
// design alone shows. Such a design keeps an inout port's two nets apart so
// that a delay annotated to the port (§32.4.4) has somewhere to sit between
// them: the lowerer links them as two nets (LinkInoutPortNets), and §23.3.3.6
// has the elaborator warn where either is a uwire (WarnUwireNetsKeptApart).
bool DesignCallsSdfAnnotate(const RtlirDesign& design);

// §23.3.3.6: the warning that port `port` of instance `inst`, with a uwire on
// either side, is not merged into a single net.
void WarnUwireNotMerged(DiagEngine& diag, SourceLoc loc, std::string_view port,
                        std::string_view inst);

// §23.3.3.6 with §23.3.3.7: in a design that calls $sdf_annotate, warns for
// each inout port binding of the elaborated `design` that joins two nets, one
// a uwire, which Elaborator::CheckUwirePortMerge counted as merged
// (RtlirPortBinding::uwire_net_join) while the design was still being
// elaborated and the call might sit in a module not yet reached. The
// warning stands at the connection. Read after a driven input port has been
// coerced to inout (§23.3.3.1), which the lowerer keeps apart as well.
void WarnUwireNetsKeptApart(const RtlirDesign& design, DiagEngine& diag);

}  // namespace delta
