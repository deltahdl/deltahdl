#pragma once

#include <cstddef>
#include <string_view>
#include <unordered_map>
#include <unordered_set>

namespace delta {

class DiagEngine;
struct Expr;
struct TypeShapeTables;
struct ModuleDecl;
struct ModuleItem;

const Expr* CheckerActualFor(const ModuleItem* item, const ModuleDecl* decl,
                             size_t i);

bool CheckerFormalAdmitsDollar(const ModuleDecl* checker, size_t i);

void ValidateCheckerActuals(const ModuleItem* item, const ModuleDecl* checker,
                            DiagEngine& diag);

void ValidateProceduralCheckerActuals(
    const ModuleItem* item, const ModuleDecl* checker,
    const std::unordered_set<std::string_view>& automatics, DiagEngine& diag);

void ValidateCheckerEnclosingRefs(
    const ModuleDecl* decl, const TypeShapeTables& tables,
    const std::unordered_map<std::string_view, const ModuleItem*>& funcs,
    DiagEngine& diag);

}  // namespace delta
