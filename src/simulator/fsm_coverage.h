#pragma once

#include "simulator/vpi_coverage.h"

namespace delta {

class CoverageControlState;
class SimContext;
struct FsmHandleRef;
struct RtlirDesign;

// §40.2.2 with §40.4 and §40.3.2.2/§40.3.2.3: count the FSM states the run
// reaches, and the transitions between them §40.2.1 lists beside them. Every
// instance of a module whose pragmas identify an FSM is given, in the run's
// coverage-control state, the number of legal states its FSMs have as its
// `SV_COV_FSM_STATE maximum, and the number of moves between two of them as
// its kCoverageTypeFsmTransition maximum, and starts collecting both; each
// write to a state signal then counts the legal state the FSM holds, once,
// and the move into it, once, while the instance collects.
void AttachFsmCoverage(const RtlirDesign* design, SimContext& ctx);

// §40.5.2: what an FSM handle or an FSM state handle stands for. An FSM's
// entities are its states: how many there are, how many it has reached, and
// the times it entered them summed; a state is one entity, reached or not,
// and the times the FSM entered it.
EntityCoverage FsmHandleCoverage(const FsmHandleRef& handle,
                                 CoverageControlState& cov);

}  // namespace delta
