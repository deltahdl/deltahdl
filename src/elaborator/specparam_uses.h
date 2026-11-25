#pragma once

namespace delta {

class DiagEngine;
struct CompilationUnit;

void ReportMisusedSpecparams(const CompilationUnit& unit, DiagEngine& diag);

}  // namespace delta
