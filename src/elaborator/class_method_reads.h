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

// §23.9: every name a declaration of a compilation unit gives, in whichever
// scope it stands: the items of the unit, of its packages and of its modules,
// interfaces, programs and checkers with their ports and parameters; the
// members, parameters and type parameters of every class, nested ones among
// them; and every enumeration constant those declare. A name read in a class
// resolves, if at all, to one of these, so one none of them gives is
// unresolved wherever it is read. The set is wider than any one scope reaches,
// so it answers whether a name is declared at all, not whether it is visible.
class UnitDeclaredNames {
 public:
  explicit UnitDeclaredNames(const CompilationUnit* unit);

  // Whether some declaration of the unit gives `name`. A §6.19.2 member
  // written `name[N]` gives the constants its name with a number appended.
  bool Declares(std::string_view name) const;

 private:
  void AddItems(const std::vector<ModuleItem*>& items);
  void AddScope(const ModuleDecl* scope);
  void AddClass(const ClassDecl* cls);
  void AddEnumerations(const DataType& type);

  std::unordered_set<std::string_view> names_;
  std::unordered_set<std::string_view> numbered_enum_names_;
};

// The names the items of a scope declare, with those of every scope nested in
// it: each named item, instance and gate, generate block and case label,
// procedural block label, loop and foreach variable, formal and procedural
// local, enumeration constant (§6.19) and implicit net (§6.10), and what a
// nested declaration declares. It holds more than any one scope declares, so a
// check consults it only to leave a name unreported.
class ScopeNameSet {
 public:
  void AddScope(const ModuleDecl* scope);
  void AddItem(const ModuleItem* item);
  void AddStmt(const Stmt* s);
  void Insert(std::string_view name);

  // Whether the set gives `name`. A §6.19.2 member written `name[N]` gives
  // the constants its name with a number appended.
  bool Contains(std::string_view name) const;

 private:
  void AddItemOwnNames(const ModuleItem* item);
  void AddEnumerations(const DataType& type);
  void AddImplicitNets(const Expr* e);

  std::unordered_set<std::string_view> names_;
  std::unordered_set<std::string_view> numbered_enum_names_;
};

// §23.8: the names the first name of a hierarchical name may resolve to. The
// search goes downward and then upward, through the scopes enclosing the
// reference and the modules instantiating them, and can end at an instance, a
// named block, a generate block, a task, a function or a module, so rather
// than follow it from each reference this answers whether any declaration of
// the unit gives the name: those of UnitDeclaredNames, with the scope names
// it leaves out -- every instance, gate and bound instance, block label,
// generate name, formal and procedural local, modport and nested declaration.
// A name it does not give is declared nowhere.
class UnitHierHeadNames {
 public:
  explicit UnitHierHeadNames(const CompilationUnit* unit);

  bool Admits(std::string_view name) const;

 private:
  UnitDeclaredNames declared_;
  ScopeNameSet scope_names_;
};

// §23.8: reports the first name of each hierarchical name the procedural
// blocks and the subroutines of `decl` write that `admits` does not accept.
// Defined in elaborator_scope_rules_hier.cpp.
void ReportUnresolvedHierHeads(
    const ModuleDecl* decl, const std::function<bool(std::string_view)>& admits,
    DiagEngine& diag);

// §23.6 with §27.4 and §27.5: reports each `g.m` or `g[k].m` the continuous
// assignments and procedural blocks of `decl` write where `g` names a generate
// block of `decl` and nothing else of it, and no block of that name declares
// `m`. Defined in elaborator_scope_rules_hier.cpp.
void ReportUndeclaredGenerateBlockMembers(const ModuleDecl* decl,
                                          DiagEngine& diag);

// §23.9: reports each name a method of a class of `unit` reads that neither
// the method declares, as a formal or in its body, nor any declaration of the
// unit gives (UnitDeclaredNames).
void ReportClassMethodUnresolved(const CompilationUnit* unit, DiagEngine& diag);

}  // namespace delta

#endif  // DELTA_ELABORATOR_CLASS_METHOD_READS_H
