#pragma once

#include <functional>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "parser/ast_module.h"

namespace delta {

// §23.11: a bind instance's parameters reached by a hierarchical name are no
// constant outside the instance; reported where a module's packed range
// reaches one, in every module at or below `tops`. `find_module` answers a
// module's declaration.
void ReportBindParamsInConstants(
    const std::vector<RtlirModule*>& tops,
    const std::function<const ModuleDecl*(std::string_view)>& find_module,
    DiagEngine& diag);

}  // namespace delta
