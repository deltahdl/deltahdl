#pragma once

namespace delta {

class Arena;
struct CompilationUnit;

void ResolvePackageAssertionNames(const CompilationUnit* unit, Arena& arena);

}  // namespace delta
