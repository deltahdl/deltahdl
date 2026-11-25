#pragma once

namespace delta {

class DiagEngine;
struct CompilationUnit;

void ReportClassSpecializationAssignments(const CompilationUnit& unit,
                                          DiagEngine& diag);

}  // namespace delta
