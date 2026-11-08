#pragma once

#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

struct CheckerInstantiationInProcedure {
  Stmt* stmt = nullptr;
  std::vector<std::string_view> locals;
};

std::vector<CheckerInstantiationInProcedure> CheckerInstantiationsIn(
    Stmt* body, DiagEngine& diag);

bool AdmitProceduralCheckerInstance(const ModuleItem* item,
                                    const ModuleDecl* child,
                                    const RtlirModule* mod, DiagEngine& diag);

}  // namespace delta
