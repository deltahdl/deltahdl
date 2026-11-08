#pragma once

#include "common/diagnostic.h"

namespace delta {

struct ModuleDecl;

void CheckNewPlacement(const ModuleDecl* decl, DiagEngine& diag);

}  // namespace delta
