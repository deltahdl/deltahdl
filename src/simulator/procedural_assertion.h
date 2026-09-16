#pragma once

#include <cstdint>
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
// next. `pending` holds the instances placed this time step that have not
// matured, each with the values it saved (§16.14.6.1); §16.14.6.2: a
// flush point of the process clears them, and the Observed region moves
// the rest to `matured`, the matured assertion queue, where a flush reaches
// them no more and every one of them begins an attempt at the next tick, a
// statement a loop reaches several times in one step beginning as many.
// The named scopes the statement was first reached in are kept for its
// reports to name, as §21.2.1.5's %m names the statement under the labels
// of the procedure.
// §16.14.6.3: a procedure run again in a later pass of the Active region
// of one time step, after the Reactive region wrote what it reads, may
// queue an instance after the statement's clock ticked in that step; the
// instance matures in the next Observed region and, the clocking event
// having occurred in the step, begins its attempt there and then, which
// `ticked_at`, the step the monitor last ticked in, tells, and `monitor`
// is the process the attempt is evaluated in.
struct ProceduralAssertionState {
  const Stmt* stmt = nullptr;
  Process* monitor = nullptr;
  std::vector<const InstanceBindings*> pending;
  std::vector<const InstanceBindings*> matured;
  bool maturing_scheduled = false;
  bool reached = false;
  uint64_t ticked_at = ~static_cast<uint64_t>(0);
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

// §16.14.6.2: `proc` has reached a procedural assertion flush point, having
// resumed after an event control or a wait statement, or as an always_comb
// or always_latch on a transition of a dependent signal, or under a disable
// of its outermost scope: its procedural assertion queue is cleared, every
// pending instance of every statement embedded in it dropped, which no
// longer matures unless the procedure queues it again; the instances that
// matured in an earlier Observed region are kept.
void FlushProceduralAssertionQueue(Process& proc);

// §16.14.6.4: a disable naming a specific procedural concurrent assertion
// of `proc`, by its label, clears the pending instances of that assertion
// alone, those of the others staying in the queue and a matured instance
// being impacted by no disable; answers whether `label` named one.
bool DisableProceduralAssertion(Process& proc, std::string_view label);

}  // namespace delta
