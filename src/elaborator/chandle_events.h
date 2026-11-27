#pragma once

#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "parser/ast_design.h"

namespace delta {

void ReportChandleEvents(const CompilationUnit& unit,
                         const TypedefMap& typedefs, DiagEngine& diag);

}  // namespace delta
