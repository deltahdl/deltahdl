#pragma once

#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "elaborator/type_param_restriction.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

struct TypeParamPrefixScope {
  const std::vector<RtlirParamDecl>& params;
  const TypedefMap& typedefs;
  const std::unordered_set<std::string_view>& class_names;
};

void ReportTypeParamPrefixNotAClass(std::string_view prefix, SourceLoc loc,
                                    const TypeParamPrefixScope& scope,
                                    DiagEngine& diag);

void ReportTypeRefPrefixNotAClass(const Expr* ref, SourceLoc loc,
                                  const TypeParamPrefixScope& scope,
                                  DiagEngine& diag);

const DataType* TypeRefThroughBoundPrefix(std::string_view prefix,
                                          std::string_view name,
                                          const TypedefMap& typedefs);

void ReportSpecializationBindingErrors(const DataType& written, SourceLoc loc,
                                       const TypeParamRestrictionScope& scope,
                                       DiagEngine& diag);

void ReportItemTypeParamErrors(const ModuleItem& item,
                               const TypeParamPrefixScope& scope,
                               const TypeParamRestrictionScope& restriction,
                               DiagEngine& diag);

void ReportUnitScopeTypeParamErrors(const TypeParamRestrictionScope& scope,
                                    DiagEngine& diag);

void ReportUnitSpecializations(const TypeParamRestrictionScope& scope,
                               DiagEngine& diag);

}  // namespace delta
