#pragma once

#include <string_view>
#include <vector>

namespace delta {

struct Expr;
struct Process;
struct RtlirModule;
class SimContext;

std::vector<Process*> ProcessesInDisabledScope(
    const Expr* name, const std::vector<Process*>& procs, SimContext& ctx);

void DeclareModuleNamedScopes(const RtlirModule& mod,
                              std::string_view inst_prefix, SimContext& ctx);

}  // namespace delta
