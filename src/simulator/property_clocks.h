#pragma once

#include <cstdint>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_stmt.h"

namespace delta {

class SimContext;

// §16.13: the clocks a property's sequences are evaluated on, numbered as
// the property meets them, the leading clock 0, and the ticks of each told
// by watchers on the signals it names, so that an evaluation woken by any
// of them knows which ticked at the time step. A property whose sequences
// name no clock of their own is on one clock, every wake of its process a
// tick of it, and installs no watcher.
struct PropertyClocks {
  std::vector<std::vector<EventExpr>> clocks;
  // The time steps each clock ticked at since the property last stepped, in
  // order. §16.9.4 takes a step of a property naming a future sampled value
  // function at the global clocking tick after its own, as of its own, so the
  // ticks are kept until the step at their time step has read them.
  std::vector<std::vector<SimTime>> ticks;
  // Whether each signal watched, one entry per event of every clock in
  // order, read true at the change before.
  std::vector<bool> was_true;
  bool multiclock = false;
  SimTime installed_at;
  static constexpr SimTime kNever{~static_cast<uint64_t>(0)};
};

// The number of `clock` among the property's, numbered where it is new; 0
// for an empty clock, the leading clock's.
int ClockIndexOf(PropertyClocks& clocks, const std::vector<EventExpr>& clock);

// Installs the watchers where the property is on more than one clock, for
// the clocks not yet watched; the time step the first is installed at is
// one of the property's evaluation, a tick of the leading clock, and reads
// as one.
void InstallClockWatchers(PropertyClocks& clocks, SimContext& ctx,
                          Arena& arena);

// The clocks that ticked at the time step `now`, a bit per clock; every bit
// where the property is on one clock.
uint32_t ClocksTicked(const PropertyClocks& clocks, SimTime now);

// Forgets the ticks before `now`, the time step the property steps at; the
// steps are taken in the order of their time steps, so none reads them again.
void ForgetTicksBefore(PropertyClocks& clocks, SimTime now);

// Whether `woke`, the event that resumed the property's process, is an event
// of one of its clocks other than the leading one and of no event of the
// leading clock.
bool WokenByAnotherClock(const PropertyClocks& clocks, const EventExpr& woke);

}  // namespace delta
