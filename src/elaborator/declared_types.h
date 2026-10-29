#pragma once

#include <functional>
#include <string_view>
#include <vector>

#include "common/source_loc.h"
#include "elaborator/aggregate_shape.h"

namespace delta {

struct CompilationUnit;
struct DataType;
struct Expr;
struct ModuleDecl;
struct ModuleItem;

// One declaration's written type: the data type and the unpacked dimensions
// after the declared name, and where the declaration stands. `nettype` is the
// declaration itself where it is a nettype's (§6.6.7), and null otherwise.
struct DeclaredType {
  const DataType& type;
  const std::vector<Expr*>& unpacked_dims;
  SourceLoc loc;
  const ModuleItem* nettype = nullptr;
};

using DeclaredTypeVisit = std::function<void(const DeclaredType&)>;

// Calls `visit` for each declaration inside the module `decl` that is not one
// of its own variables, typedefs or nettypes, which are judged as they are
// elaborated: its ports, a variable or nettype a procedural block declares, a
// subroutine's return and arguments and the variables and nettypes its body
// declares, and a property, typedef, nettype or method of a class declared in
// the module, at any depth of nesting.
void ForEachInnerDeclaredType(const ModuleDecl* decl,
                              const DeclaredTypeVisit& visit);

// The same for what no module's elaboration reaches: the compilation unit's
// variables, nettypes and classes, each package's variables, typedefs and
// nettypes, and every declaration inside the subroutines and classes of
// either. The compilation unit's typedefs are judged on their own.
void ForEachUnitDeclaredType(const CompilationUnit* unit,
                             const DeclaredTypeVisit& visit);

// The rules on a declaration's type that hold wherever it is written: §7.2 to
// §7.3.2 on a structure or union type (CheckAggregateShape), §7.8.5 on an
// associative index type (CheckRealAssocIndexTypes) and, for a nettype's,
// §6.6.7 on the data types a nettype may name (ReportIllegalNettypeDataType),
// `names_covergroup` answering for the covergroups the declaration sees.
void CheckDeclaredTypeRules(
    const DeclaredType& declared, const AggregateShapeCtx& ctx,
    const std::function<bool(std::string_view)>& names_covergroup = {});

}  // namespace delta
