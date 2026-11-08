#pragma once

#include <string_view>
#include <unordered_set>

#include "elaborator/const_eval.h"

namespace delta {

class DiagEngine;
class PropertyRegistry;
struct ModuleDecl;
struct ModuleInUnit;
struct ModuleItem;
struct RtlirModule;
struct Stmt;

std::unordered_set<std::string_view> CollectItemAutomaticVarNames(
    const ModuleItem* item);

const Stmt* FindConcurrentAssertionInPassStmt(const Stmt* s);

void ValidateAssertionRules(const ModuleDecl* decl,
                            const PropertyRegistry& registry, DiagEngine& diag);

void ValidateAssertionExprRules(const ModuleInUnit& scope,
                                const RtlirModule* mod, const ScopeMap& params,
                                const PropertyRegistry& registry,
                                DiagEngine& diag);

void ValidateAssertionBoundRules(const ModuleDecl* decl, const ScopeMap& params,
                                 DiagEngine& diag);

void ValidateAssertionContextRules(const ModuleDecl* decl,
                                   const RtlirModule* mod,
                                   const PropertyRegistry& registry,
                                   DiagEngine& diag);

void ValidateLocalVariableFlow(const ModuleDecl* decl, DiagEngine& diag);

}  // namespace delta
