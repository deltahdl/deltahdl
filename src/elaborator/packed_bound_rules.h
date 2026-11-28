#pragma once

#include <functional>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/source_loc.h"
#include "elaborator/type_eval.h"
#include "parser/ast_type.h"

namespace delta {

class DiagEngine;
struct ClassDecl;
struct CompilationUnit;
struct Expr;
struct ModuleItem;

using RealParamKinds = std::unordered_map<std::string_view, DataTypeKind>;

struct PackedBoundNames {
  std::function<bool(const Expr*)> names_variable;
  std::function<bool(const Expr*)> calls_non_constant_function;
  const RealParamKinds& real_params;
  std::function<bool(const Expr*)> names_xz_constant;
};

bool NamesPackageVariable(const Expr* e, const CompilationUnit* unit);

void ReportPackedBounds(const DataType& dtype, SourceLoc loc,
                        const PackedBoundNames& names, DiagEngine& diag);

void ReportPackedBoundsOfItem(const ModuleItem& item, bool with_declarations,
                              const PackedBoundNames& names, DiagEngine& diag);

void ReportPackedBoundsInScope(const std::vector<ModuleItem*>& items,
                               const CompilationUnit* unit,
                               const TypedefMap& typedefs, DiagEngine& diag);

void ReportPackedBoundsInClass(const ClassDecl& cls,
                               const CompilationUnit* unit,
                               const TypedefMap& typedefs, DiagEngine& diag);

}  // namespace delta
