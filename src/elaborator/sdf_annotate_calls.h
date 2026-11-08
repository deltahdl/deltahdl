#pragma once

#include <string_view>

#include "common/source_loc.h"

namespace delta {

class DiagEngine;
struct RtlirDesign;

bool DesignCallsSdfAnnotate(const RtlirDesign& design);

void WarnUwireNotMerged(DiagEngine& diag, SourceLoc loc, std::string_view port,
                        std::string_view inst);

void WarnUwireNetsKeptApart(const RtlirDesign& design, DiagEngine& diag);

}  // namespace delta
