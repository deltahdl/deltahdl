#pragma once

#include <functional>
#include <string_view>

namespace delta {

class DiagEngine;
struct CompilationUnit;
struct ModuleDecl;

void ReportCallsOfDataNames(
    const ModuleDecl& decl, const CompilationUnit& unit,
    const std::function<bool(std::string_view)>& visible, DiagEngine& diag);

void ReportClassMethodCalls(const CompilationUnit& unit, DiagEngine& diag);

}  // namespace delta
