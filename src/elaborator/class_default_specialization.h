#pragma once

#include "common/source_loc.h"

namespace delta {

class DiagEngine;
struct CompilationUnit;
struct DataType;

void ReportSpecializationWithoutValue(const DataType& named, SourceLoc loc,
                                      const CompilationUnit& unit,
                                      DiagEngine& diag);

void ReportClassSpecializationsWithoutValues(const CompilationUnit& unit,
                                             DiagEngine& diag);

}  // namespace delta
