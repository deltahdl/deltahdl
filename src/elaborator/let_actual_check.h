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

// What the check of a let's actuals reads besides the declarations it walks:
// the compilation unit, the typedef tables a type's members and dimensions are
// sized with, the parameter values of the design element checked, where the
// reports go, the arena a class's specialized type is built in, and whether
// the design element assumes §6.10's implicit nets, which `default_nettype
// none forbids (§22.8) and which the compilation unit and the packages, with
// no instance or continuous assignment, never declare.
struct LetActualContext {
  const CompilationUnit* unit;
  const TypeShapeTables& shapes;
  const ScopeMap& parameters;
  DiagEngine& diag;
  Arena& arena;
  bool implicit_nets;
};

// §11.12, rule 2: a typed let formal other than an event takes an actual cast
// compatible (§6.22.4) with the formal's type, the default the declaration
// gives included. Each call `decl` writes is judged against the let its name
// reaches through the scopes around the call (§23.9, §26.3): a block's or a
// generate block's, the design element's own, an import's, or one of
// `unit_items`, the compilation unit's items written ahead of `decl`
// (§3.12.1). A call is reported only where the let it names, the variable its
// actual names and both their types are known.
void CheckLetActualsOfDesignElement(const ModuleDecl& decl,
                                    const std::vector<ModuleItem*>& unit_items,
                                    const LetActualContext& ctx);

// The same rule for the compilation unit's own items and each package's: the
// defaults of their lets and the calls their subroutines and declarations
// write, each judged once rather than in every design element.
void CheckLetActualsOfUnitAndPackages(const LetActualContext& ctx);

}  // namespace delta
