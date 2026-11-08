#pragma once

#include <functional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace delta {

struct Expr;
struct Stmt;
struct EventExpr;
struct ModuleItem;
struct ModuleDecl;
struct CompilationUnit;
class Arena;

using FuncMap = std::unordered_map<std::string_view, const ModuleItem*>;

struct InferenceFuncs {
  FuncMap funcs;
  std::unordered_map<std::string_view, std::unordered_set<std::string_view>>
      class_names;
};

void CollectExprReads(const Expr* expr, std::unordered_set<std::string>& out);

bool DottedNamePath(const Expr* expr, std::string& out);

void ForEachStmtReadExpr(const Stmt* stmt,
                         const std::function<void(const Expr*)>& fn);

void CollectStmtReads(const Stmt* stmt, std::unordered_set<std::string>& out);

void CollectWrittenNames(const Stmt* stmt,
                         std::unordered_set<std::string>& out);

std::vector<EventExpr> InferSensitivity(
    const Stmt* body, Arena& arena, const InferenceFuncs* calls = nullptr,
    bool exclude_written = true,
    const std::unordered_set<std::string_view>* const_names = nullptr);

struct ScopedCallSite {
  const std::vector<const ModuleDecl*>& decl_path;
  const CompilationUnit& unit;
  const std::function<const ModuleDecl*(std::string_view)>& find_module;
};

void AddScopedCallFunctions(const Stmt* body, const ScopedCallSite& site,
                            Arena& arena, InferenceFuncs& calls);

}  // namespace delta
