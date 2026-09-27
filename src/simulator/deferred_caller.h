#pragma once

#include <memory>

namespace delta {

class SimContext;
struct Process;

// §21.2.2 (printed page 664) with §8.6 and §8.11: $strobe, $monitor and their
// file forms produce their text at the end of a time step, long after the call
// that asked for it, yet the text is the call's arguments read as the calling
// scope sees them -- inside a class method that is the method's object, its
// class, and the method's own locals as well as the instance the call was
// written in. A stand-in process carries all of that from the call to the
// write: the caller's instance and generate prefixes, its named scopes, and a
// copy of the object, class and local-scope stacks it was running with. It is
// never a thread of the run (§37.44); SetCurrentProcess does not note it.
// Returns null for a call made outside any process.
std::shared_ptr<Process> SnapshotCallingProcess(SimContext& ctx);

// Installs `caller` (a SnapshotCallingProcess result, or null) as the running
// process for its lifetime and puts the process it displaced back after, so a
// deferred write reads its arguments in the caller's context. The stand-in's
// stacks travel back into it as the other process returns, so it can serve
// every write of a monitor that writes many times.
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
