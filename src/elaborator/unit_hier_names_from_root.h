#pragma once

#include "elaborator/elaborator_scope_rules_names.h"

namespace delta {

class DiagEngine;
struct CompilationUnit;
struct RtlirDesign;

// §3.12.1 (printed page 56): for upward name referencing the compilation-unit
// scope is a top-level design element, so a hierarchical name one of its tasks
// or functions writes, headed by a name the unit neither declares nor imports,
// is a full path from the top of the design ($root, §23.3.1) and is never
// searched for from where the subroutine is called. Reports each such name
// whose first name is no top-level instance of `design`: `u.x` naming an
// instance of a caller names nothing.
void ReportUnitHierNamesFromRoot(const CompilationUnit& unit,
                                 const RtlirDesign& design,
                                 ProvidedNameCache& provided_cache,
                                 DiagEngine& diag);

}  // namespace delta
