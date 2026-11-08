#pragma once

#include <functional>
#include <string_view>

namespace delta {

class DiagEngine;
struct ModuleDecl;

void ReportAssertionUnresolved(
    const ModuleDecl* decl,
    const std::function<bool(std::string_view)>& declared, DiagEngine& diag);

void ReportNonConstantBoundActuals(
    const ModuleDecl* decl,
    const std::function<bool(std::string_view)>& is_variable, DiagEngine& diag);

}  // namespace delta
