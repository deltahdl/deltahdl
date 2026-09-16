#pragma once

#include <string_view>
#include <vector>

#include "common/arena.h"
#include "simulator/instance_bindings.h"

namespace delta {

struct Process;
class SimContext;
struct Stmt;

// §16.14.6: the procedural assertion queue of one concurrent assertion
// statement embedded in one process. A statement reached in procedural code
// is not evaluated where it stands: the process places a pending instance
// of it here, the instances mature in the Observed region, and each begins
// an evaluation attempt at the tick of the statement's leading clocking
// event that the time step holds or, where the step holds none, at the
// next, so `pending` holds the instances placed since the last tick, each
// with the values it saved (§16.14.6.1), and every one of them begins an
// attempt at the next, a statement a loop reaches several times in one step
// beginning as many. The named scopes the statement was first reached in
// are kept for its reports to name, as §21.2.1.5's %m names the statement
// under the labels of the procedure.
struct ProceduralAssertionState {
  std::vector<const InstanceBindings*> pending;
  bool reached = false;
  std::vector<std::string_view> named_scopes;
};

// §16.14.6: starts, for each concurrent assertion embedded in `body` that
// carries a leading clocking event, the monitor process that evaluates the
// statement for `proc`: it wakes at every occurrence of the clocking event
// and, in the Observed region of that time step, advances the attempts in
// flight and begins one for each pending instance in the queue, which the
// process fills as it reaches the statement. Called as the process is
// lowered, so the monitor stands armed before the first clock tick.
void StartProceduralAssertionMonitors(Process* proc, const Stmt* body,
                                      SimContext& ctx, Arena& arena);

// §16.14.6: places one pending instance of `stmt` in the queue the current
// process keeps for it, with, §16.14.6.1, the value of each const cast and
// each automatic variable of its property and action block saved as they
// stand now; answers false where the process keeps no queue, one the
// lowerer started no monitor for, so that the caller evaluates the statement
// where it stands.
bool EnqueueProceduralAssertion(const Stmt* stmt, SimContext& ctx,
                                Arena& arena);

}  // namespace delta
