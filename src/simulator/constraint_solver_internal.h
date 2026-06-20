#pragma once

#include <vector>

#include "simulator/constraint_solver.h"

namespace delta {

// 18.5.13.2: classify the active constraints into the hard relations to satisfy
// and the soft preferences to honor, omitting 'disable soft' directives (which
// are resolved separately). Walks every enabled block in declaration order and
// then the inline 'extra' constraints last, the order that fixes
// soft-constraint priority. Shared between constraint_solver_eval.cpp (which
// defines it) and constraint_solver_solve.cpp.
void CollectConstraints(const std::vector<ConstraintBlock>& blocks,
                        const std::vector<ConstraintExpr>& extra,
                        std::vector<const ConstraintExpr*>& hard,
                        std::vector<const ConstraintExpr*>& soft);

}  // namespace delta
