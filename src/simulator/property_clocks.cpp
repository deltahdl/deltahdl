#include "simulator/property_clocks.h"

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

namespace delta {

namespace {

// Whether two clocks are the same event: the same edges over signals of
// the same spelling.
bool SameClock(const std::vector<EventExpr>& a,
               const std::vector<EventExpr>& b) {
  if (a.size() != b.size()) return false;
  for (size_t i = 0; i < a.size(); ++i) {
    if (a[i].edge != b[i].edge) return false;
    if (a[i].signal == nullptr || b[i].signal == nullptr) return false;
    if (a[i].signal->text != b[i].signal->text) return false;
  }
  return true;
}

// §9.4.2: whether the change from `was` to `now` is the edge the event
// names, a posedge the rise to true, a negedge the fall from it, and an
// event with no edge any change.
bool EdgeHappened(Edge edge, bool was, bool now) {
  switch (edge) {
    case Edge::kPosedge:
      return !was && now;
    case Edge::kNegedge:
      return was && !now;
    case Edge::kEdge:
    case Edge::kNone:
      return was != now;
  }
  return false;
}

// The variable the event's signal names, where it names one.
Variable* SignalOf(const EventExpr& ev, SimContext& ctx) {
  if (ev.signal == nullptr || ev.signal->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  return ctx.FindVariable(ev.signal->text);
}

// Watches one event of the clock numbered `clock`: at each change of its
// signal, the edge the event names records the time step as a tick.
void WatchEvent(PropertyClocks& clocks, int clock, size_t slot,
                const EventExpr& ev, SimContext& ctx, Arena& arena) {
  Variable* var = SignalOf(ev, ctx);
  if (var == nullptr) return;
  clocks.was_true[slot] = EvalExpr(ev.signal, ctx, arena).IsTruthy();
  var->AddWatcher([&clocks, clock, slot, &ev, &ctx, &arena]() {
    bool now = EvalExpr(ev.signal, ctx, arena).IsTruthy();
    bool was = clocks.was_true[slot];
    clocks.was_true[slot] = now;
    if (EdgeHappened(ev.edge, was, now)) {
      clocks.ticked_at[clock] = ctx.CurrentTime();
    }
    return false;
  });
}

}  // namespace

int ClockIndexOf(PropertyClocks& clocks, const std::vector<EventExpr>& clock) {
  if (clock.empty()) return 0;
  for (size_t i = 0; i < clocks.clocks.size(); ++i) {
    if (SameClock(clocks.clocks[i], clock)) return static_cast<int>(i);
  }
  clocks.clocks.push_back(clock);
  return static_cast<int>(clocks.clocks.size() - 1);
}

void InstallClockWatchers(PropertyClocks& clocks, SimContext& ctx,
                          Arena& arena) {
  clocks.multiclock = clocks.clocks.size() > 1;
  if (!clocks.multiclock) return;
  clocks.installed_at = ctx.CurrentTime();
  clocks.ticked_at.assign(clocks.clocks.size(), PropertyClocks::kNever);
  size_t events = 0;
  for (const auto& clock : clocks.clocks) events += clock.size();
  clocks.was_true.assign(events, false);
  size_t slot = 0;
  for (size_t i = 0; i < clocks.clocks.size(); ++i) {
    for (const EventExpr& ev : clocks.clocks[i]) {
      WatchEvent(clocks, static_cast<int>(i), slot++, ev, ctx, arena);
    }
  }
}

uint32_t ClocksTicked(const PropertyClocks& clocks, SimTime now) {
  if (!clocks.multiclock) return ~0u;
  uint32_t ticked = now == clocks.installed_at ? 1u : 0u;
  for (size_t i = 0; i < clocks.ticked_at.size() && i < 32; ++i) {
    if (clocks.ticked_at[i] == now) ticked |= 1u << i;
  }
  return ticked;
}

}  // namespace delta
