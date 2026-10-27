#pragma once

#include <string_view>
#include <vector>

namespace delta {

struct Expr;
struct Process;
struct RtlirModule;
class SimContext;

// §9.6.2 with §23.8: the processes among `procs` that stand in the block or
// task the disable written as `name` ends. Each of `procs` stands in a scope
// of the name's last component, and the scope the name resolves to is the
// first, nearest first, that the design declares or one of them stands in,
// none of them standing in a declared one nothing runs in: a scope the running
// process stands in holding the name, from the innermost back to the
// procedure or subroutine it runs, then its generate blocks, innermost first,
// its instance and the instances holding that one, and last a path headed by a
// top-level module's name. With no process running, `procs` are left as they
// are.
std::vector<Process*> ProcessesInDisabledScope(
    const Expr* name, const std::vector<Process*>& procs, SimContext& ctx);

// §9.6.2 with §23.8: declares to `ctx` (DeclareNamedScope) every named block,
// labelled statement and subroutine the module `mod` declares, lowered as the
// instance `inst_prefix`, under the key ProcessesInDisabledScope reads a
// process's scopes by, so that a disable's search ends at the nearest scope
// of its name whether or not anything runs in it.
void DeclareModuleNamedScopes(const RtlirModule& mod,
                              std::string_view inst_prefix, SimContext& ctx);

}  // namespace delta
