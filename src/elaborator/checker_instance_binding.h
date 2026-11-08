#pragma once

#include <cstdint>
#include <optional>
#include <string_view>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/expr_substitute.h"

namespace delta {

ModuleDecl* PackageCheckerNamedBy(const ModuleItem* item,
                                  const RtlirModule* mod,
                                  const CompilationUnit* unit);

void CheckCheckerInstForm(const ModuleItem* item, const ModuleDecl* child,
                          DiagEngine& diag);

using BoundCheckerFormals =
    std::vector<std::pair<std::string_view, std::optional<int64_t>>>;

using ConstantCheckerFormals =
    std::vector<std::pair<std::string_view, int64_t>>;

BoundCheckerFormals BindCheckerActuals(const ModuleItem* item,
                                       const ModuleDecl* decl,
                                       const ScopeMap& scope);

ActualsByFormal CheckerTreeActuals(const ModuleItem* item,
                                   const ModuleDecl* decl);

void ReportActualsOnlyACheckerTakes(const RtlirModuleInst& inst,
                                    const ModuleItem* item, DiagEngine& diag);

ConstantCheckerFormals CheckerConstantFormals(const ModuleDecl* decl,
                                              const BoundCheckerFormals& bound,
                                              const ScopeMap& scope);

void SetCheckerFreeVariables(const ModuleDecl* decl, RtlirModule* mod);

}  // namespace delta
