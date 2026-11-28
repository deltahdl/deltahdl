#pragma once

#include <functional>
#include <vector>

#include "elaborator/rtlir_scopes.h"
#include "elaborator/type_eval.h"

namespace delta {

struct ClassDecl;
struct CompilationUnit;
struct DataType;
struct Expr;
struct ModuleItem;
struct RtlirModule;
struct RtlirParamDecl;

using NamesXzConstant = std::function<bool(const Expr*)>;

struct XzConstantScope {
  const CompilationUnit* unit;
  const TypedefMap& typedefs;
};

struct ParamValueScopes {
  const GenBlockPrefixes& own;
  const GenBlockPrefixes& instantiating;
};

bool ValueReachesXZ(const Expr* e, const NamesXzConstant& names_xz_constant);

bool ScopeConstantHoldsXZ(const Expr* name,
                          const std::vector<ModuleItem*>& items,
                          const XzConstantScope& scope);

bool ClassConstantHoldsXZ(const Expr* name, const ClassDecl& cls,
                          const XzConstantScope& scope);

bool ModuleConstantHoldsXZ(const Expr* name, const RtlirModule& mod,
                           const GenBlockPrefixes& scopes,
                           const XzConstantScope& scope);

bool ParamValueHoldsXZ(const RtlirParamDecl& pd, const DataType* declared,
                       const RtlirModule& mod, const ParamValueScopes& scopes,
                       const XzConstantScope& scope);

}  // namespace delta
