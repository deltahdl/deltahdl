#pragma once

// IEEE 1800-2023 §40.5.2 and §40.5.3: what vpi_get(), vpi_handle() and
// vpi_control() read and do on the handles of single coverable items - an
// assertion, a statement, a signal, an FSM and an FSM state - out of the
// coverage the run collects of each (code_coverage.h).

#include <optional>

#include "simulator/coverage_control.h"
#include "simulator/vpi_design_attach_build.h"

namespace delta {

struct VpiObject;

// §40.5.2: vpi_get() of vpiCovered, vpiCoveredCount or vpiCoveredMax on an
// assertion, statement, signal, FSM or FSM state handle, and of an
// assertion-specific coverage status property on an assertion handle;
// nothing for any other property or handle. `stmts` are the model's
// statement objects, which a statement handle is found among.
std::optional<int> VpiItemCoverage(VpiObject* obj, int property,
                                   const VpiStmtObjects& stmts,
                                   CoverageControlState& cov);

// §40.5.2: vpi_handle(vpiFsmStateExpression, fsm_handle), the signal or
// expression holding the FSM's state; true where `type` is that relation, the
// answer in `out`.
bool TryResolveFsmRelation(int type, VpiObject* ref, VpiObject*& out);

// §40.5.3: vpi_control() of `control` over the coverage of `coverage_type`,
// a §40.5.1 property, of the one assertion `assertion` is the handle of. Only
// assertion coverage is controlled per assertion; any other type, controlled
// per instance alone, is a bad argument here.
int VpiControlAssertionCoverage(CoverageControl control, int coverage_type,
                                VpiObject& assertion,
                                CoverageControlState& cov);

}  // namespace delta
