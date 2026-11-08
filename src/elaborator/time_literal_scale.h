#pragma once

#include "common/types.h"

namespace delta {

struct CompilationUnit;
struct ModuleDecl;
struct PackageDecl;

TimeScale CompilationUnitTimescale(const CompilationUnit& unit);

TimeScale ModuleTimescale(const ModuleDecl* decl, const CompilationUnit& unit);

TimeScale PackageTimescale(const PackageDecl& pkg, const TimeScale& unit_scale);

void ScaleTimeLiterals(const CompilationUnit& unit);

}  // namespace delta
