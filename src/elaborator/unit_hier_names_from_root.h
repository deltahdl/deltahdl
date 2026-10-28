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

// §3.12.1 (printed page 57): no hierarchical reference reaches an identifier
// the compilation-unit scope declares. Reports each hierarchical name of
// names joined by `.` that the instances of `design` write in their procedural
// blocks, continuous assignments, initializers and subroutines, or that the
// tasks and functions of `unit` write, whose path ends at an instance that
// does not declare the name the path gives next, where the unit declares it.
// The path is read from $root when `$root.` heads it, and otherwise from the
// enclosing module its first name names (§23.8) or from the top-level instance
// of that name, a scope the referencing module declares under the name taking
// the name from both.
void ReportHierNamesReachingTheUnit(const CompilationUnit& unit,
                                    const RtlirDesign& design,
                                    DiagEngine& diag);

}  // namespace delta
