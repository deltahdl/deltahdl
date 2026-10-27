#pragma once

#include <vector>

namespace delta {

struct Expr;
struct Process;
class SimContext;

// §9.6.2 with §23.8: the processes among `procs` that stand in the block or
// task the disable written as `name` ends. Each of `procs` stands in a scope
// of the name's last component, and the scope the name resolves to is the
// first, nearest first, that one of them stands in: a scope the running
// process stands in holding the name, from the innermost back to the
// procedure or subroutine it runs, then its generate blocks, innermost first,
// its instance and the instances holding that one, and last a path headed by a
// top-level module's name. With no process running, `procs` are left as they
// are.
std::vector<Process*> ProcessesInDisabledScope(
    const Expr* name, const std::vector<Process*>& procs, SimContext& ctx);

}  // namespace delta
