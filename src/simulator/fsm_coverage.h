#pragma once

namespace delta {

struct RtlirDesign;
class SimContext;

// §40.2.2 with §40.4 and §40.3.2.2/§40.3.2.3: count the FSM states the run
// reaches. Every instance of a module whose pragmas identify an FSM is given,
// in the run's coverage-control state, the number of legal states its FSMs
// have as its `SV_COV_FSM_STATE maximum, and starts collecting; each write to
// a state signal then counts the legal state the FSM holds, once, while the
// instance collects, as its current `SV_COV_FSM_STATE coverage.
void AttachFsmCoverage(const RtlirDesign* design, SimContext& ctx);

}  // namespace delta
