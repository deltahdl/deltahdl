#pragma once

#include "common/diagnostic.h"

namespace delta {

struct ModuleDecl;

void CheckUntypedDefaultPatternValues(const ModuleDecl* decl, DiagEngine& diag);

}  // namespace delta
