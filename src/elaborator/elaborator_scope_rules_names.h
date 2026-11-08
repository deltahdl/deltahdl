#pragma once

#include <cstddef>
#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

namespace delta {

void CollectBareIdents(const Expr* e, std::vector<const Expr*>& out);

struct ProvidedNameHash {
  using is_transparent = void;
  size_t operator()(std::string_view name) const noexcept {
    return std::hash<std::string_view>{}(name);
  }
};

using ProvidedNames = std::unordered_map<std::string, std::string_view,
                                         ProvidedNameHash, std::equal_to<>>;

void PopulatePackageProvidedNames(const CompilationUnit* unit,
                                  std::string_view pkg_name,
                                  ProvidedNames& names);

using ProvidedNameCache = std::unordered_map<std::string_view, ProvidedNames>;

bool PackageDeclared(const CompilationUnit* unit, std::string_view pkg_name);

std::string_view ProvidedNameOrigin(const CompilationUnit* unit,
                                    ProvidedNameCache& provided_cache,
                                    std::string_view pkg_name,
                                    std::string_view name);

bool PackageProvidesName(const CompilationUnit* unit,
                         ProvidedNameCache& provided_cache,
                         std::string_view pkg_name, std::string_view name);

bool ImportsProvideName(const CompilationUnit* unit,
                        ProvidedNameCache& provided_cache,
                        const std::vector<ModuleItem*>& items,
                        std::string_view name);

std::vector<std::string_view> WildcardImportedPackages(const RtlirModule* mod);

void CollectModuleGenerateNames(const std::vector<ModuleItem*>& items,
                                std::unordered_set<std::string_view>& names);

void CollectProcLocalNames(const Stmt* s,
                           std::unordered_set<std::string_view>& names);

void CollectProcVariableNames(const Stmt* s,
                              std::unordered_set<std::string_view>& names);

bool ArgNamesDesignElement(const Expr* e);

void CollectRandsequenceDeclaredNames(
    const Stmt* s, std::unordered_set<std::string_view>& names);

void CollectProcReadableNames(const Stmt* s,
                              std::unordered_set<std::string_view>& names);

void CollectProcRhsIdents(const Stmt* s,
                          const std::unordered_set<std::string_view>& locals,
                          std::vector<const Expr*>& out);

std::unordered_set<std::string_view> MatchesBindingsOf(const Expr* e);

std::vector<std::string_view> ForHeaderDeclaredNames(const Stmt* s);

void ForEachChildStmtWithBindings(
    const Stmt* s,
    const std::function<
        void(const Stmt*, const std::unordered_set<std::string_view>&)>& visit);

void CollectSubroutineLocalNames(const ModuleItem* item,
                                 std::unordered_set<std::string_view>& names);

struct UnitScopeNames {
  const std::unordered_set<std::string_view>& item_names;
  const ScopeMap& constants;
  const TypedefMap& typedefs;
  const std::unordered_set<std::string_view>& class_names;
};

void ReportUnresolvedInUnitSubroutines(const CompilationUnit* unit,
                                       const UnitScopeNames& names,
                                       ProvidedNameCache& provided_cache,
                                       DiagEngine& diag);

void ReportUnresolvedInPackageSubroutines(const CompilationUnit* unit,
                                          const UnitScopeNames& names,
                                          ProvidedNameCache& provided_cache,
                                          DiagEngine& diag);

}  // namespace delta
