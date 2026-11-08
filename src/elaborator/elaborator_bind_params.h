#pragma once

#include <functional>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "parser/ast_module.h"

namespace delta {

void ReportBindParamsInConstants(
    const std::vector<RtlirModule*>& tops,
    const std::function<const ModuleDecl*(std::string_view)>& find_module,
    DiagEngine& diag);

}  // namespace delta
