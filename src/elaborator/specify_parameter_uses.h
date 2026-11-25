#pragma once

namespace delta {

class DiagEngine;
struct CompilationUnit;

void ReportParametersUsedInSpecifyBlocks(const CompilationUnit& unit,
                                         DiagEngine& diag);

}  // namespace delta
