#pragma once

#include <optional>

#include "simulator/coverage_control.h"
#include "simulator/vpi_design_attach_build.h"

namespace delta {

struct VpiObject;

std::optional<int> VpiItemCoverage(VpiObject* obj, int property,
                                   const VpiStmtObjects& stmts,
                                   CoverageControlState& cov);

bool TryResolveFsmRelation(int type, VpiObject* ref, VpiObject*& out);

int VpiControlAssertionCoverage(CoverageControl control, int coverage_type,
                                VpiObject& assertion,
                                CoverageControlState& cov);

}  // namespace delta
