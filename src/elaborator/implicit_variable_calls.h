#pragma once

namespace delta {

class DiagEngine;
struct CompilationUnit;

void ReportBareCallsAsImplicitVariables(const CompilationUnit& unit,
                                        DiagEngine& diag);

}  // namespace delta
