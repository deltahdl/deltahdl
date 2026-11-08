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

struct CompilationUnitSet {
  std::vector<CompilationUnit*> units;
  std::vector<CompilationUnit*> views;
  CompilationUnit* merged = nullptr;
  std::unordered_map<const ModuleDecl*, size_t> owner;
  std::vector<std::shared_ptr<UnitScopeTables>> tables;
  size_t current = 0;
};

CompilationUnitSet PoolCompilationUnits(
    const std::vector<CompilationUnit*>& units, Arena& arena);

}  // namespace delta
