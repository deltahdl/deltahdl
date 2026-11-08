#pragma once

#include "common/diagnostic.h"
#include "parser/ast_module.h"

namespace delta {

struct CompilationUnit;
struct TypeShapeTables;

void ValidateCheckerProcedureCovergroups(const ModuleDecl* decl,
                                         DiagEngine& diag);

void ValidateCheckerAssignmentCalls(const ModuleDecl* decl, DiagEngine& diag);

bool HasArgumentWrittenBack(const ModuleItem* fn);

bool FunctionIsImpure(const ModuleItem* fn);

void ValidateCheckerFormalDefaults(const ModuleDecl* decl, DiagEngine& diag);

void ValidateCheckerInterfaceFormals(const ModuleDecl* decl,
                                     const CompilationUnit* unit,
                                     const TypeShapeTables& types,
                                     DiagEngine& diag);

}  // namespace delta
