#pragma once

#include <string_view>
#include <vector>

namespace delta {

class DiagEngine;
class Elaborator;
struct CompilationUnit;
struct ConfigDecl;
struct RtlirDesign;

std::vector<const ConfigDecl*> ConfigsInForce(const CompilationUnit& unit);

RtlirDesign* ElaborateCommandLine(Elaborator& elab, const CompilationUnit& unit,
                                  std::string_view top, std::string_view config,
                                  DiagEngine& diag);

}  // namespace delta
