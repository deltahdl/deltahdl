#include "elaborator/unit_hier_names_from_root.h"

#include <cstddef>
#include <format>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/class_method_reads.h"
#include "elaborator/elaborator_scope_rules_names.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// The names the compilation-unit scope of `unit` declares: its items' own,
// the classes it declares, and the enumeration constants its types declare.
std::unordered_set<std::string_view> UnitScopeOwnNames(
    const CompilationUnit& unit) {
  std::unordered_set<std::string_view> names;
  for (const ModuleItem* item : unit.cu_items) {
    names.insert(item->name);
    if (item->class_decl != nullptr) names.insert(item->class_decl->name);
    for (const DataType* type : {&item->data_type, &item->typedef_type}) {
      for (const EnumMember& member : type->enum_members)
        names.insert(member.name);
    }
  }
  return names;
}

// The names the path `e` joins, first to last, where it is a path of names
// joined by `.` alone; false where a select, a call, a `::` or any other
// operation stands in it.
bool PathNames(const Expr* e, std::vector<const Expr*>& names) {
  if (e->kind == ExprKind::kIdentifier) {
    names.push_back(e);
    return true;
  }
  if (e->kind != ExprKind::kMemberAccess || e->is_scope_resolution ||
      !PathNames(e->lhs, names)) {
    return false;
  }
  names.push_back(e->rhs);
  return true;
}

// The names `decl` declares within itself, its own name aside: the parameters
// of its header, its ports, and what its items declare, an instance, a named
// or generate block and a nested declaration among them.
ScopeNameSet ScopeContents(const ModuleDecl* decl) {
  ScopeNameSet names;
  for (const auto& param : decl->params) names.Insert(param.first);
  for (const PortDecl& port : decl->ports) names.Insert(port.name);
  for (const ModuleItem* item : decl->items) names.AddItem(item);
  return names;
}

// The walk ReportHierNamesReachingTheUnit makes. `chain` holds the instance
// whose code is read and the instances above it, the top-level one first.
class UnitPathCheck {
 public:
  using Chain = std::vector<const RtlirModule*>;

  UnitPathCheck(const CompilationUnit& unit, const RtlirDesign& design,
                DiagEngine& diag)
      : unit_names_(UnitScopeOwnNames(unit)), design_(design), diag_(diag) {}

  void CheckInstance(const RtlirModule* mod, Chain& chain) {
    if (mod == nullptr) return;
    chain.push_back(mod);
    CheckItems(mod->decl->items, chain);
    for (const RtlirModuleInst& child : mod->children)
      CheckInstance(child.resolved, chain);
    chain.pop_back();
  }

  // §3.12.1 (printed page 56): the compilation-unit scope is a top-level
  // design element, so a path its subroutines write is read from the top.
  void CheckItems(const std::vector<ModuleItem*>& items, const Chain& chain) {
    for (const ModuleItem* item : items) {
      CheckStmt(item->body, chain);
      for (const Stmt* s : item->func_body_stmts) CheckStmt(s, chain);
      CheckExpr(item->assign_lhs, chain);
      CheckExpr(item->assign_rhs, chain);
      CheckExpr(item->init_expr, chain);
    }
  }

 private:
  void CheckStmt(const Stmt* s, const Chain& chain) {
    if (s == nullptr) return;
    ForEachChildExpr(s, [&](const Expr* e) { CheckExpr(e, chain); });
    ForEachChildStmt(s, [&](Stmt* const& sub) { CheckStmt(sub, chain); });
  }

  // A path's own operands are the shorter paths it extends, so a path is
  // read whole and not descended into.
  void CheckExpr(const Expr* e, const Chain& chain) {
    if (e == nullptr) return;
    std::vector<const Expr*> names;
    if (PathNames(e, names)) {
      std::string_view prefix = names.front()->scope_prefix;
      if (prefix == "$root" || (prefix.empty() && names.size() > 1))
        CheckPath(names, chain);
      return;
    }
    ForEachExprChild(e, [&](const Expr* sub) { CheckExpr(sub, chain); });
  }

  // Follows the path down through the instances its names name, from $root
  // (null) or from the instance its first name names, and reports the first
  // name no instance gives where the instance reached declares no such name
  // and the unit does.
  void CheckPath(const std::vector<const Expr*>& names, const Chain& chain) {
    const RtlirModule* scope = nullptr;
    size_t next = 0;
    if (names.front()->scope_prefix.empty()) {
      scope = HeadInstance(names.front()->text, chain);
      if (scope == nullptr) return;
      next = 1;
    }
    for (size_t i = next; i < names.size(); ++i) {
      std::string_view name = names[i]->text;
      if (const RtlirModule* child = Step(scope, name)) {
        scope = child;
        continue;
      }
      if (unit_names_.contains(name) && !Declares(scope, name))
        Report(names, i);
      return;
    }
  }

  // §23.8: the instance the first name of a path names, searched for from the
  // referencing instance upward by the name of each instance's module, then
  // among the top-level instances. Null where a scope on the way declares the
  // name, so the path is read from something this walk does not follow.
  const RtlirModule* HeadInstance(std::string_view name, const Chain& chain) {
    for (auto it = chain.rbegin(); it != chain.rend(); ++it) {
      if (ContentsOf((*it)->decl).Contains(name)) return nullptr;
      if ((*it)->decl->name == name) return *it;
    }
    return Step(nullptr, name);
  }

  // The instance `name` names below `scope`, the top-level instances being
  // those below $root (null).
  const RtlirModule* Step(const RtlirModule* scope,
                          std::string_view name) const {
    if (scope == nullptr) {
      for (const RtlirModule* top : design_.top_modules) {
        if (top->name == name) return top;
      }
      return nullptr;
    }
    for (const RtlirModuleInst& child : scope->children) {
      if (child.inst_name == name) return child.resolved;
    }
    return nullptr;
  }

  bool Declares(const RtlirModule* scope, std::string_view name) {
    return scope != nullptr && ContentsOf(scope->decl).Contains(name);
  }

  const ScopeNameSet& ContentsOf(const ModuleDecl* decl) {
    auto it = contents_.find(decl);
    if (it == contents_.end())
      it = contents_.emplace(decl, ScopeContents(decl)).first;
    return it->second;
  }

  // One report per path, however many instances of its module there are.
  void Report(const std::vector<const Expr*>& names, size_t last) {
    if (!reported_.insert(names.front()).second) return;
    std::string path = names.front()->scope_prefix.empty() ? "" : "$root.";
    for (size_t i = 0; i <= last; ++i) {
      if (i != 0) path += '.';
      path += names[i]->text;
    }
    diag_.Error(names.front()->range.start,
                std::format("hierarchical name '{}' is unresolved: '{}' is "
                            "declared in the compilation-unit scope, which no "
                            "hierarchical name reaches",
                            path, names[last]->text),
                Subclause("3.12.1"));
  }

  std::unordered_set<std::string_view> unit_names_;
  const RtlirDesign& design_;
  DiagEngine& diag_;
  std::unordered_map<const ModuleDecl*, ScopeNameSet> contents_;
  std::unordered_set<const Expr*> reported_;
};

}  // namespace

void ReportUnitHierNamesFromRoot(const CompilationUnit& unit,
                                 const RtlirDesign& design,
                                 ProvidedNameCache& provided_cache,
                                 DiagEngine& diag) {
  std::unordered_set<std::string_view> reached = UnitScopeOwnNames(unit);
  for (const RtlirModule* top : design.top_modules) reached.insert(top->name);
  for (const Expr* head : UnitSubroutineHierHeads(unit)) {
    if (reached.contains(head->text) ||
        ImportsProvideName(&unit, provided_cache, unit.cu_items, head->text)) {
      continue;
    }
    diag.Error(head->range.start,
               std::format("hierarchical name '{}' in a compilation-unit task "
                           "or function is read from $root, where no "
                           "top-level instance '{}' stands",
                           head->text, head->text),
               Subclause("3.12.1"));
  }
}

void ReportHierNamesReachingTheUnit(const CompilationUnit& unit,
                                    const RtlirDesign& design,
                                    DiagEngine& diag) {
  UnitPathCheck check(unit, design, diag);
  UnitPathCheck::Chain chain;
  for (const RtlirModule* top : design.top_modules)
    check.CheckInstance(top, chain);
  check.CheckItems(unit.cu_items, chain);
}

}  // namespace delta
