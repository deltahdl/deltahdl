#pragma once

#include <string_view>
#include <vector>

#include "common/source_loc.h"

namespace delta {

class DiagEngine;
struct CompilationUnit;
struct ModuleDecl;
struct ModuleItem;

bool PrecedesInText(SourceLoc a, SourceLoc b);

bool UnitDeclaresData(const CompilationUnit* unit, std::string_view name,
                      SourceLoc reference);

const ModuleItem* UnitNetBefore(const CompilationUnit* unit,
                                std::string_view name, SourceLoc reference);

bool UnitDataDeclaredOnlyAfter(const CompilationUnit* unit,
                               std::string_view name, SourceLoc reference);

bool UnitDeclaresConstant(const CompilationUnit* unit, std::string_view name,
                          SourceLoc reference);

bool UnitConstantDeclaredOnlyAfter(const CompilationUnit* unit,
                                   std::string_view name, SourceLoc reference);

bool ModuleDeclaresName(const ModuleDecl* decl, std::string_view name);

std::vector<ModuleItem*> UnitItemsBefore(const CompilationUnit* unit,
                                         SourceLoc reference);

void ReportUnitScopedReferences(const std::vector<ModuleItem*>& items,
                                const CompilationUnit* unit, DiagEngine& diag);

void ReportReferencesBeforePackages(const CompilationUnit* unit,
                                    DiagEngine& diag);

}  // namespace delta
