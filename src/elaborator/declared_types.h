#pragma once

#include <functional>
#include <vector>

#include "common/source_loc.h"
#include "elaborator/aggregate_shape.h"

namespace delta {

struct CompilationUnit;
struct DataType;
struct Expr;
struct ModuleDecl;

// One declaration's written type: the data type and the unpacked dimensions
// after the declared name, and where the declaration stands.
struct DeclaredType {
  const DataType& type;
  const std::vector<Expr*>& unpacked_dims;
  SourceLoc loc;
};

using DeclaredTypeVisit = std::function<void(const DeclaredType&)>;

// Calls `visit` for each declaration inside the module `decl` that is not one
// of its own variables or typedefs, which are judged as they are elaborated:
// its ports, a variable a procedural block declares, a subroutine's return and
// arguments and the variables its body declares, and a property, typedef or
// method of a class declared in the module, at any depth of nesting.
void ForEachInnerDeclaredType(const ModuleDecl* decl,
                              const DeclaredTypeVisit& visit);

// The same for what no module's elaboration reaches: the compilation unit's
// variables and classes, each package's variables and typedefs, and every
// declaration inside the subroutines and classes of either. The compilation
// unit's typedefs are judged on their own.
void ForEachUnitDeclaredType(const CompilationUnit* unit,
                             const DeclaredTypeVisit& visit);

// The rules on a declaration's type that hold wherever it is written: §7.2 to
// §7.3.2 on a structure or union type (CheckAggregateShape) and §7.8.5 on an
// associative index type (CheckRealAssocIndexTypes).
void CheckDeclaredTypeRules(const DeclaredType& declared,
                            const AggregateShapeCtx& ctx);

}  // namespace delta
