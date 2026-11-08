#pragma once

#include <vector>

namespace delta {

class Arena;
class PropertyRegistry;
struct CompilationUnit;
struct ModuleDecl;
struct ModuleItem;

struct RunDeclarations {
  std::vector<ModuleItem*>& properties;
  std::vector<ModuleItem*>& sequences;
};

void RegisterInterfaceInstanceProperties(const ModuleDecl* decl,
                                         const CompilationUnit* unit,
                                         PropertyRegistry& registry,
                                         Arena& arena, RunDeclarations run);

}  // namespace delta
