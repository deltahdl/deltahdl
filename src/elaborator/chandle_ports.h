#pragma once

#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "parser/ast_module.h"

namespace delta {

void ReportChandlePorts(const ModuleDecl& decl, const TypedefMap& typedefs,
                        DiagEngine& diag);

}  // namespace delta
