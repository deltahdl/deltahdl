#pragma once

namespace delta {

class DiagEngine;
struct CompilationUnit;

// §33.3.1.1 (printed page 937): of the modules, interfaces, programs and
// primitives of one name that `unit` maps into one library, the one encountered
// last is the one written to the library, so the others are dropped from
// `unit`. Each module of a name after the first that its library was given is
// warned about, since every one comes from this invocation.
void WriteCellsToLibraries(CompilationUnit& unit, DiagEngine& diag);

}  // namespace delta
