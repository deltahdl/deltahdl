#pragma once

#include "common/diagnostic.h"
#include "elaborator/net_data_type.h"

namespace delta {

struct CompilationUnit;

void CheckClassParamDollarValues(const CompilationUnit* unit,
                                 const TypeShapeTables& tables,
                                 DiagEngine& diag);

}  // namespace delta
