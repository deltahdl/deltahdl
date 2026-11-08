#pragma once

#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"

namespace delta {

struct CompilationUnit;
struct Expr;
struct ModuleDecl;

bool IsLoneDollar(const Expr* e);

bool ContainsDollar(const Expr* e);

void CheckDollarOperands(const ModuleDecl* decl, const CompilationUnit& unit,
                         const std::unordered_set<std::string_view>& unbounded,
                         DiagEngine& diag);

void CheckUnitDollarOperands(const CompilationUnit& unit, DiagEngine& diag);

}  // namespace delta
