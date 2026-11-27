#pragma once

#include <vector>

namespace delta {

class Arena;
struct CompilationUnit;

void ResolveEnumBaseTypedefs(const std::vector<CompilationUnit*>& units,
                             Arena& arena);

}  // namespace delta
