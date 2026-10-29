#pragma once

#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

namespace delta {

// §6.6.8 (printed page 99): whether `e` is a net_lvalue every net and port of
// which is an interconnect `names` holds: such a name under selects whose
// indices read no interconnect, or a concatenation or assignment pattern of
// those. A.8.5 writes no net_lvalue in parentheses.
bool IsInterconnectNetLvalue(const Expr* e,
                             const std::unordered_set<std::string_view>& names);

// §6.6.8: an interconnect may express a port or terminal connection, as an
// all-interconnect net_lvalue, and may appear in no other expression. Reports
// the instance `item` -- of a module, interface or program, or of a gate,
// switch or UDP -- where a port connection or terminal uses an interconnect
// of `names` and is no such net_lvalue, or where a parameter value, a delay
// or the range of an instance array uses one at all.
void ReportInterconnectInInstance(
    const ModuleItem& item, const std::unordered_set<std::string_view>& names,
    DiagEngine& diag);

}  // namespace delta
