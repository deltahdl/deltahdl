#pragma once

#include <cstddef>
#include <memory>
#include <unordered_map>
#include <vector>

namespace delta {

class Arena;
struct CompilationUnit;
struct ModuleDecl;
struct UnitScopeTables;

// §3.12.1 (printed page 56): the compilation units of a compilation in which
// each file is a unit of its own. Modules, primitives, programs, interfaces and
// packages are visible in every unit, so each unit is read through a view that
// pools those of every unit beside its own compilation-unit scope, and the
// merged view pools the units' scopes too, for what is checked once over the
// whole design. Holds no view where the compilation is a single unit.
struct CompilationUnitSet {
  // The units as parsed, each holding its own declarations alone.
  std::vector<CompilationUnit*> units;
  std::vector<CompilationUnit*> views;
  CompilationUnit* merged = nullptr;
  // The unit that declared each design element, as an index into views.
  std::unordered_map<const ModuleDecl*, size_t> owner;
  // Each unit's compilation-unit-scope tables, one per view.
  std::vector<std::shared_ptr<UnitScopeTables>> tables;
  // The unit whose tables are in force, or views.size() where the merged
  // view's are.
  size_t current = 0;
};

// The views of `units`, made in `arena`. `units` holds at least one unit.
CompilationUnitSet PoolCompilationUnits(
    const std::vector<CompilationUnit*>& units, Arena& arena);

}  // namespace delta
