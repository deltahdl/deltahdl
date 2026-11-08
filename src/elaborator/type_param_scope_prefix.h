#pragma once

#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
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

void ReportSpecializationPrefixNotAClass(const DataType& written, SourceLoc loc,
                                         const CompilationUnit* unit,
                                         DiagEngine& diag);

void ReportItemPrefixesNotAClass(const ModuleItem& item,
                                 const TypeParamPrefixScope& scope,
                                 DiagEngine& diag);

void ReportUnitScopePrefixesNotAClass(const CompilationUnit* unit,
                                      DiagEngine& diag);

void ReportUnitSpecializations(const CompilationUnit* unit, DiagEngine& diag);

}  // namespace delta
