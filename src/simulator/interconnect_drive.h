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

struct InterconnectTransition {
  uint64_t ticks = 0;
  Logic4Vec value;
  Logic4Vec bits;
  std::shared_ptr<bool> superseded = std::make_shared<bool>(false);
};

struct InterconnectShadow;

struct InterconnectSchedule {
  std::vector<std::shared_ptr<InterconnectTransition>> pending;
  std::shared_ptr<InterconnectShadow> shadow;
};

struct InterconnectShadow {
  Net net;
  Variable resolved;
  std::vector<std::shared_ptr<InterconnectSchedule>> per_driver;
  bool alive = true;
};

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

ExecTask AwaitInterconnectArrivals(const InterconnectSchedule& schedule,
                                   SimContext& ctx);

struct InterconnectChange {
  const Logic4Vec& held;
  const Logic4Vec& value;
  const Logic4Vec& bits;
};

void DriveAcrossInterconnect(
    const std::shared_ptr<InterconnectSchedule>& schedule,
    const InterconnectDelay& delay, const InterconnectChange& change,
    SimContext& ctx, const std::function<void(const Logic4Vec&)>& commit);

struct InterconnectEnds {
  std::string source;
  std::string load;
};

void FollowNetDrivers(Net& net,
                      const std::shared_ptr<InterconnectShadow>& shadow,
                      InterconnectEnds ends, SimContext& ctx,
                      std::function<void(const Logic4Vec&)> commit);

}  // namespace delta
