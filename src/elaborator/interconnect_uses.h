#pragma once

#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

bool IsInterconnectNetLvalue(const Expr* e,
                             const std::unordered_set<std::string_view>& names);

void ReportInterconnectInInstance(
    const ModuleItem& item, const std::unordered_set<std::string_view>& names,
    DiagEngine& diag);

}  // namespace delta
