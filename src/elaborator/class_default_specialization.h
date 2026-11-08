#pragma once

#include <string_view>

namespace delta {

class DiagEngine;
struct ClassDecl;
struct CompilationUnit;

std::string_view ParameterWithoutDefault(const ClassDecl& cls);

void ReportUnadornedClassesWithoutDefaults(const CompilationUnit& unit,
                                           DiagEngine& diag);

}  // namespace delta
