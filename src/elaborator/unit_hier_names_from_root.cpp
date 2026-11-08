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

ScopeNameSet ScopeContents(const ModuleDecl* decl) {
  ScopeNameSet names;
  for (const auto& param : decl->params) names.Insert(param.first);
  for (const PortDecl& port : decl->ports) names.Insert(port.name);
  for (const ModuleItem* item : decl->items) names.AddItem(item);
  return names;
}

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

  const RtlirModule* HeadInstance(std::string_view name, const Chain& chain) {
    for (auto it = chain.rbegin(); it != chain.rend(); ++it) {
      if (ContentsOf((*it)->decl).Contains(name)) return nullptr;
      if ((*it)->decl->name == name) return *it;
    }
    return Step(nullptr, name);
  }

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
