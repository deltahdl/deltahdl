#pragma once

#include "elaborator/elaborator_scope_rules_names.h"

namespace delta {

class DiagEngine;
struct CompilationUnit;
struct RtlirDesign;

void ReportUnitHierNamesFromRoot(const CompilationUnit& unit,
                                 const RtlirDesign& design,
                                 ProvidedNameCache& provided_cache,
                                 DiagEngine& diag);

void ReportHierNamesReachingTheUnit(const CompilationUnit& unit,
                                    const RtlirDesign& design,
                                    DiagEngine& diag);

}  // namespace delta
