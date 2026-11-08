#pragma once

#include <functional>
#include <string_view>

#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"

namespace delta {

void ReportDataUsedAboveItsDeclaration(
    const ModuleDecl& decl, const RtlirModule& mod, const CompilationUnit& unit,
    const std::function<bool(std::string_view)>& enclosing, DiagEngine& diag);

void ReportDataUsedAboveItsDeclaration(const CompilationUnit& unit,
                                       DiagEngine& diag);

}  // namespace delta
