#pragma once

#include <cstdint>
#include <functional>
#include <memory>
#include <string>
#include <vector>

#include "common/types.h"
#include "simulator/exec_task.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/specify_sdf.h"
#include "simulator/variable.h"

namespace delta {

// §32.4.4: one transition of a port connection on its way across an annotated
// interconnect delay to the load. `value` is what the connection commits when
// it arrives at `ticks`, `bits` the part of it the connection drives, which is
// what a later transition is measured from. `superseded` is set when §30.7's
// pulse rules drop it before it arrives, or the connection goes away, and the
// scheduler then treats its arrival as no event at all.
struct InterconnectTransition {
  uint64_t ticks = 0;
  Logic4Vec value;
  Logic4Vec bits;
  std::shared_ptr<bool> superseded = std::make_shared<bool>(false);
};

struct InterconnectShadow;

// §32.4.4: the transitions of one port connection still to reach its load, in
// the order they arrive. An interconnect delay allows any number of them, each
// scheduled when its source changed. `shadow` is the load's own view of a
// multisource net it is connected to, where it follows one.
struct InterconnectSchedule {
  std::vector<std::shared_ptr<InterconnectTransition>> pending;
  std::shared_ptr<InterconnectShadow> shadow;
};

// §32.4.4: a load's own view of the net its connection reads: the net's
// drivers as they have reached the load, each across the interconnect delay
// from the port it stands for, resolved as the net resolves its own. On a
// multisource net each source/load pair may carry a delay of its own, which
// the net's one resolved value cannot show. `alive` is cleared when the
// connection goes away.
struct InterconnectShadow {
  Net net;
  Variable resolved;
  std::vector<std::shared_ptr<InterconnectSchedule>> per_driver;
  bool alive = true;
};

// Supersedes every transition still pending when the connection that owns the
// schedule ends, in whatever way it ends, so none commits into a connection
// that is gone.
struct InterconnectScheduleOwner {
  std::shared_ptr<InterconnectSchedule> schedule =
      std::make_shared<InterconnectSchedule>();
  InterconnectScheduleOwner() = default;
  InterconnectScheduleOwner(const InterconnectScheduleOwner&) = delete;
  InterconnectScheduleOwner& operator=(const InterconnectScheduleOwner&) =
      delete;
  ~InterconnectScheduleOwner() {
    for (const auto& transition : schedule->pending) {
      *transition->superseded = true;
    }
    if (schedule->shadow != nullptr) schedule->shadow->alive = false;
  }
};

// §32.4.4: suspends until every transition pending on `schedule` has reached
// the load, waking at the time of the last of them and never after it, so a
// connection that has no further change to wait for lets them all arrive
// before it ends.
ExecTask AwaitInterconnectArrivals(const InterconnectSchedule& schedule,
                                   SimContext& ctx);

// One change of a port connection's source: the part of the load the
// connection drives as it stands, the connection's new value, and the part of
// that value the connection drives.
struct InterconnectChange {
  const Logic4Vec& held;
  const Logic4Vec& value;
  const Logic4Vec& bits;
};

// §32.4.4 with §30.7: carries `change` across the interconnect delay `delay`
// to the connection's load; `commit` places a value on the load.
//
// The transition takes the delay and the limits of Table 32-4's slot for the
// change from where the load is heading to `bits`. Where it follows a pending
// one closer than that pending one's own lead, the two edges are a pulse at
// the load, and its trailing edge's limits decide it as §30.7 has a module
// path's decided: rejected, both edges vanish; filtered, the leading edge
// becomes x; otherwise both arrive. A transition scheduled earlier than the
// one before it crosses it, and the one before it is dropped.
void DriveAcrossInterconnect(
    const std::shared_ptr<InterconnectSchedule>& schedule,
    const InterconnectDelay& delay, const InterconnectChange& change,
    SimContext& ctx, const std::function<void(const Logic4Vec&)>& commit);

// §32.4.4: the two names a port connection's interconnect delay is annotated
// between -- the signal it reads and the port it drives.
struct InterconnectEnds {
  std::string source;
  std::string load;
};

// §32.4.4: keeps `shadow` following every driver of `net` for the connection
// named by `ends`, which commits to its load through `commit`. While the load
// carries no delay of its own from any one source a written driver is mirrored
// at once, the connection carrying the net's resolved value as before; once it
// does, each driver reaches the shadow across the delay from the port it stands
// for (Net::driver_ports), or, for one standing for no port, the delay the
// connection's own source name is asked about, and the shadow's resolution is
// what reaches the load.
void FollowNetDrivers(Net& net,
                      const std::shared_ptr<InterconnectShadow>& shadow,
                      InterconnectEnds ends, SimContext& ctx,
                      std::function<void(const Logic4Vec&)> commit);

}  // namespace delta
