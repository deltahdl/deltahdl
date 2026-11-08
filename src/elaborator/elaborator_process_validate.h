#pragma once

#include <string>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/rtlir.h"
#include "parser/ast_module.h"

namespace delta {

void ValidateProcess(RtlirProcessKind kind, ModuleItem* item,
                     const RtlirProcess& proc, DiagEngine& diag,
                     const std::unordered_set<std::string>& task_names);

}  // namespace delta
