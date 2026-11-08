#ifndef DELTA_ELABORATOR_CLASS_METHOD_READS_H
#define DELTA_ELABORATOR_CLASS_METHOD_READS_H

#include <functional>
#include <string_view>
#include <unordered_set>
#include <vector>

namespace delta {

class DiagEngine;
struct ClassDecl;
struct CompilationUnit;
struct DataType;
struct Expr;
struct ModuleDecl;
struct ModuleItem;
struct Stmt;

class UnitDeclaredNames {
 public:
  explicit UnitDeclaredNames(const CompilationUnit* unit);

  bool Declares(std::string_view name) const;

 private:
  void AddItems(const std::vector<ModuleItem*>& items);
  void AddScope(const ModuleDecl* scope);
  void AddClass(const ClassDecl* cls);
  void AddEnumerations(const DataType& type);

  std::unordered_set<std::string_view> names_;
  std::unordered_set<std::string_view> numbered_enum_names_;
};

class ScopeNameSet {
 public:
  void AddScope(const ModuleDecl* scope);
  void AddItem(const ModuleItem* item);
  void AddStmt(const Stmt* s);
  void Insert(std::string_view name);

  bool Contains(std::string_view name) const;

 private:
  void AddItemOwnNames(const ModuleItem* item);
  void AddEnumerations(const DataType& type);
  void AddImplicitNets(const Expr* e);

  std::unordered_set<std::string_view> names_;
  std::unordered_set<std::string_view> numbered_enum_names_;
};

class UnitHierHeadNames {
 public:
  explicit UnitHierHeadNames(const CompilationUnit* unit);

  bool Admits(std::string_view name) const;

 private:
  UnitDeclaredNames declared_;
  ScopeNameSet scope_names_;
};

void ReportUnresolvedHierHeads(
    const ModuleDecl* decl, const std::function<bool(std::string_view)>& admits,
    DiagEngine& diag);

std::vector<const Expr*> UnitSubroutineHierHeads(const CompilationUnit& unit);

void ReportUndeclaredGenerateBlockMembers(const ModuleDecl* decl,
                                          DiagEngine& diag);

std::unordered_set<std::string_view> UnnamedGenerateBlockNames(
    const ModuleDecl* decl);

void ReportUnnamedGenerateBlockReaches(const ModuleDecl* decl,
                                       DiagEngine& diag);

void ReportClassMethodUnresolved(const CompilationUnit* unit, DiagEngine& diag);

}  // namespace delta

#endif
