#pragma once

#include <memory>

namespace delta {

class SimContext;
struct Process;

std::shared_ptr<Process> SnapshotCallingProcess(SimContext& ctx);

class CallerStandIn {
 public:
  CallerStandIn(Process* caller, SimContext& ctx);
  ~CallerStandIn();
  CallerStandIn(const CallerStandIn&) = delete;
  CallerStandIn& operator=(const CallerStandIn&) = delete;

 private:
  SimContext& ctx_;
  Process* displaced_;
};

}  // namespace delta
