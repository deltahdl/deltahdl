#pragma once

#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"

namespace delta {

struct ModuleDecl;

void CheckUnboundedParamsInQueueContexts(
    const ModuleDecl* decl,
    const std::unordered_set<std::string_view>& unbounded,
    const std::unordered_set<std::string_view>& queues, DiagEngine& diag);

void CheckDollarOperands(const ModuleDecl* decl, DiagEngine& diag);

}  // namespace delta
