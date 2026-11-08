#pragma once

namespace delta {

class SimContext;
struct Process;

void TerminateProcess(Process& proc, SimContext& ctx);

}  // namespace delta
