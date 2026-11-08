#pragma once

#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/net_data_type.h"

namespace delta {

class Arena;
class DiagEngine;
struct CompilationUnit;
struct ModuleDecl;
struct ModuleItem;

struct LetActualContext {
  const CompilationUnit* unit;
  const TypeShapeTables& shapes;
  const ScopeMap& parameters;
  DiagEngine& diag;
  Arena& arena;
  bool implicit_nets;
};

void CheckLetActualsOfDesignElement(const ModuleDecl& decl,
                                    const std::vector<ModuleItem*>& unit_items,
                                    const LetActualContext& ctx);

void CheckLetActualsOfUnitAndPackages(const LetActualContext& ctx);

}  // namespace delta
