#pragma once

namespace delta {

class SimContext;
struct Process;

// §9.7 with §9.6.2 and §9.6.3: ends `proc` forcibly, as kill(), a disable or a
// disable fork does. The process is KILLED, every await() on it returns, and,
// for a process a fork spawned, it is released from that fork's join and
// wait-fork tallies (Process::ReleaseFromFork). The release is scheduled in
// the current time step rather than run here, since it may resume the forking
// process, which must not run inside the statement doing the killing. Does
// nothing to a process already FINISHED or KILLED.
void TerminateProcess(Process& proc, SimContext& ctx);

}  // namespace delta
