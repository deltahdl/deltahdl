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

struct InstanceParams {
  std::unordered_set<std::string_view> unbounded;
  std::unordered_set<std::string_view> overridden;
};

void CheckDollarOperands(const ModuleDecl* decl, const CompilationUnit& unit,
                         const InstanceParams& instance, DiagEngine& diag);

void CheckUnitDollarOperands(const CompilationUnit& unit, DiagEngine& diag);

}  // namespace delta
