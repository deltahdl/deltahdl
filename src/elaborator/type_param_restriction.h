#pragma once

#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/type_eval.h"
#include "parser/ast_design.h"
#include "parser/ast_type.h"

namespace delta {

struct TypeParamRestrictionScope {
  const TypedefMap& typedefs;
  const CompilationUnit* unit;
  const std::unordered_set<std::string_view>& class_names;
};

struct RestrictedTypeParam {
  std::string_view name;
  DataTypeKind restriction = DataTypeKind::kImplicit;
};

void ReportTypeOutsideRestriction(const RestrictedTypeParam& param,
                                  const DataType& assigned, SourceLoc loc,
                                  const TypeParamRestrictionScope& scope,
                                  DiagEngine& diag);

void ReportClassTypeParamsOutsideRestrictions(
    const TypeParamRestrictionScope& scope, DiagEngine& diag);

void ReportSpecializationOutsideRestrictions(
    const DataType& written, SourceLoc loc,
    const TypeParamRestrictionScope& scope, DiagEngine& diag);

}  // namespace delta
