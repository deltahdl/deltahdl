#pragma once

namespace delta {

class DiagEngine;
struct CompilationUnit;

void WriteCellsToLibraries(CompilationUnit& unit, DiagEngine& diag);

}  // namespace delta
