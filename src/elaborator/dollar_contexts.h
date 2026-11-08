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

void CheckUnboundedParamsInQueueContexts(
    const ModuleDecl* decl,
    const std::unordered_set<std::string_view>& unbounded,
    const std::unordered_set<std::string_view>& queues, DiagEngine& diag);

void CheckDollarOperands(const ModuleDecl* decl, const CompilationUnit& unit,
                         DiagEngine& diag);

void CheckUnitDollarOperands(const CompilationUnit& unit, DiagEngine& diag);

}  // namespace delta
