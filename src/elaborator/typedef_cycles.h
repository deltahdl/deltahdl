#pragma once

#include <vector>

#include "common/diagnostic.h"

namespace delta {

struct CompilationUnit;

void BreakTypedefCycles(const std::vector<CompilationUnit*>& units,
                        DiagEngine& diag);

}  // namespace delta
