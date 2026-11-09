#include "elaborator/elaborator_validate_classes.h"

#include <algorithm>
#include <format>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/type_param_scope_prefix.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

struct AccessSite {
  std::vector<const ClassDecl*> inside;
  std::unordered_set<std::string_view> locals;

  bool SeesLocal(const ClassDecl* owner) const {
    return std::ranges::find(inside, owner) != inside.end();
  }

  bool SeesProtected(const ClassDecl* owner,
                     const CompilationUnit* unit) const {
    return std::ranges::any_of(inside, [&](const ClassDecl* c) {
      return IsClassDerivedFrom(c->name, owner->name, unit);
    });
  }

  const ClassDecl* ClassNamedBy(std::string_view name,
                                const CompilationUnit* unit) const {
    if (inside.empty()) return nullptr;
    if (name == "this") return inside.front();
    return name == "super" ? FindBaseClass(inside.front(), unit) : nullptr;
  }
};

}  // namespace

static void ReportHiddenMember(const OwnedMember& found, SourceLoc loc,
                               const AccessSite& site,
                               const CompilationUnit* unit, DiagEngine& diag) {
  const ClassMember* m = found.member;
  if (m && m->is_local && !site.SeesLocal(found.owner)) {
    diag.Error(loc, "cannot access local member from outside its class",
               Subclause("8.18"));
  } else if (m && m->is_protected && !site.SeesProtected(found.owner, unit)) {
    diag.Error(loc,
               "cannot access protected member from outside "
               "its class hierarchy",
               Subclause("8.18"));
  }
}

static OwnedMember ScopedClassMember(const Expr* e,
                                     const CompilationUnit* unit) {
  if (e->rhs->kind != ExprKind::kIdentifier) return {};
  const std::vector<const ClassDecl*> kChain =
      ClassChainOfScopePrefix(e->lhs, unit);
  return kChain.empty() ? OwnedMember{}
                        : FindMemberAndOwner(kChain.back(), e->rhs->text, unit);
}

static const ClassDecl* HandleClassOfBase(
    const Expr* base,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const AccessSite& site, const CompilationUnit* unit) {
  if (base->kind == ExprKind::kIdentifier) {
    auto it = var_types.find(base->text);
    if (it != var_types.end()) return FindClassDecl(it->second, unit);
    return site.ClassNamedBy(base->text, unit);
  }
  if (base->kind != ExprKind::kMemberAccess || !base->is_scope_resolution ||
      !base->lhs || !base->rhs) {
    return nullptr;
  }
  const std::vector<const ClassDecl*> kChain =
      ClassChainOfScopePrefix(base->lhs, unit);
  if (kChain.empty() || base->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  const ClassMember* m =
      FindMemberInClass(kChain.back(), base->rhs->text, unit);
  if (!m || m->kind != ClassMemberKind::kProperty) return nullptr;
  return ClassOfDeclaredType(m->data_type, kChain, unit);
}

static void CheckMemberAccessVisibility(
    const Expr* e,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const AccessSite& site, const CompilationUnit* unit, DiagEngine& diag) {
  if (e->rhs->kind != ExprKind::kIdentifier) return;
  const auto* cls = HandleClassOfBase(e->lhs, var_types, site, unit);
  if (!cls) return;

  if (cls->type_param_names.count(e->rhs->text) > 0) {
    diag.Error(e->rhs->range.start,
               "cannot access type parameter via class handle",
               Subclause("8.5"));
    return;
  }
  ReportHiddenMember(FindMemberAndOwner(cls, e->rhs->text, unit),
                     e->rhs->range.start, site, unit, diag);
}

static void CheckScopedMemberVisibility(const Expr* e, const AccessSite& site,
                                        const CompilationUnit* unit,
                                        DiagEngine& diag) {
  const OwnedMember kFound = ScopedClassMember(e, unit);
  ReportHiddenMember(kFound, e->rhs->range.start, site, unit, diag);
  const ClassMember* m = kFound.member;
  const bool kWithinHierarchy =
      m != nullptr && !site.inside.empty() &&
      IsClassDerivedFrom(site.inside.front()->name, kFound.owner->name, unit);
  if (m != nullptr && !kWithinHierarchy && !m->is_static && !m->is_param &&
      m->name != "new" &&
      (m->kind == ClassMemberKind::kProperty ||
       m->kind == ClassMemberKind::kMethod)) {
    diag.Error(e->rhs->range.start,
               std::format("cannot reach non-static member '{}' through the "
                           "class scope operator from outside its class",
                           e->rhs->text),
               Subclause("8.23"));
  }
}

static bool BasesKnown(const ClassDecl* cls, const CompilationUnit* unit) {
  for (const ClassDecl* c = cls; !c->base_class.empty();) {
    c = FindBaseClass(c, unit);
    if (c == nullptr) return false;
  }
  return true;
}

static void CheckRandomizeArgItemVisibility(const Expr* arg,
                                            const ClassDecl* cls,
                                            const AccessSite& site,
                                            const CompilationUnit* unit,
                                            DiagEngine& diag) {
  if (!arg || arg->kind != ExprKind::kIdentifier) return;
  const OwnedMember kFound = FindMemberAndOwner(cls, arg->text, unit);
  const ClassMember* m = kFound.member;
  if (m == nullptr && arg->text != "null" && BasesKnown(cls, unit)) {
    diag.Error(arg->range.start,
               std::format("'{}' is no property of class '{}', so randomize() "
                           "cannot name it as a random variable",
                           arg->text, cls->name),
               Subclause("18.11"));
  } else if (m && m->is_local && !site.SeesLocal(kFound.owner)) {
    diag.Error(arg->range.start,
               "cannot change random mode of local member from outside "
               "its class",
               Subclause("18.11"));
  } else if (m && m->is_protected && !site.SeesProtected(kFound.owner, unit)) {
    diag.Error(arg->range.start,
               "cannot change random mode of protected member from "
               "outside its class hierarchy",
               Subclause("18.11"));
  }
}

static void CheckRandomizeArgVisibility(
    const Expr* e,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const AccessSite& site, const CompilationUnit* unit, DiagEngine& diag) {
  const Expr* recv = e->lhs;
  if (!recv || recv->kind != ExprKind::kMemberAccess || !recv->lhs ||
      !recv->rhs)
    return;
  if (recv->rhs->kind != ExprKind::kIdentifier ||
      recv->rhs->text != "randomize")
    return;
  if (recv->lhs->kind != ExprKind::kIdentifier) return;
  auto it = var_types.find(recv->lhs->text);
  if (it == var_types.end()) return;
  const auto* cls = FindClassDecl(it->second, unit);
  if (!cls) return;
  for (const auto* arg : e->args) {
    CheckRandomizeArgItemVisibility(arg, cls, site, unit, diag);
  }
}

static void CheckVisibilityExpr(
    const Expr* e,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const AccessSite& site, const CompilationUnit* unit, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess && e->lhs && e->rhs) {
    if (e->is_scope_resolution) {
      CheckScopedMemberVisibility(e, site, unit, diag);
    } else {
      CheckMemberAccessVisibility(e, var_types, site, unit, diag);
    }
  }
  if (e->kind == ExprKind::kIdentifier && !site.inside.empty() &&
      !site.locals.contains(e->text)) {
    ReportHiddenMember(FindMemberAndOwner(site.inside.front(), e->text, unit),
                       e->range.start, site, unit, diag);
  }
  if (e->kind == ExprKind::kCall) {
    CheckRandomizeArgVisibility(e, var_types, site, unit, diag);
  }
  CheckVisibilityExpr(e->lhs, var_types, site, unit, diag);
  if (e->kind != ExprKind::kMemberAccess) {
    CheckVisibilityExpr(e->rhs, var_types, site, unit, diag);
  }
  CheckVisibilityExpr(e->base, var_types, site, unit, diag);
  CheckVisibilityExpr(e->index, var_types, site, unit, diag);
  CheckVisibilityExpr(e->condition, var_types, site, unit, diag);
  CheckVisibilityExpr(e->true_expr, var_types, site, unit, diag);
  CheckVisibilityExpr(e->false_expr, var_types, site, unit, diag);
  for (const auto* arg : e->args)
    CheckVisibilityExpr(arg, var_types, site, unit, diag);
}

static bool IsBareNew(const Expr* e) {
  return e != nullptr && e->kind == ExprKind::kCall && e->text == "new";
}

static void CheckConstructorAccess(std::string_view name, SourceLoc loc,
                                   const AccessSite& site,
                                   const CompilationUnit* unit,
                                   DiagEngine& diag) {
  const ClassDecl* cls = FindClassDecl(name, unit);
  if (cls == nullptr) return;
  for (const ClassMember* m : cls->members) {
    if (m->method != nullptr && m->method->name == "new") {
      ReportHiddenMember({m, cls}, loc, site, unit, diag);
    }
  }
}

static void WalkStmtsForVisibility(
    const Stmt* s,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const AccessSite& site, const CompilationUnit* unit, DiagEngine& diag) {
  if (!s) return;
  CheckVisibilityExpr(s->lhs, var_types, site, unit, diag);
  CheckVisibilityExpr(s->rhs, var_types, site, unit, diag);
  CheckVisibilityExpr(s->expr, var_types, site, unit, diag);
  CheckVisibilityExpr(s->condition, var_types, site, unit, diag);
  if (IsBareNew(s->rhs)) {
    const auto kTarget = var_types.find(ExprIdent(s->lhs));
    if (kTarget != var_types.end()) {
      CheckConstructorAccess(kTarget->second, s->range.start, site, unit, diag);
    }
  }
  if (s->kind == StmtKind::kVarDecl && IsBareNew(s->var_init)) {
    CheckConstructorAccess(s->var_decl_type.type_name, s->range.start, site,
                           unit, diag);
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkStmtsForVisibility(sub, var_types, site, unit, diag);
  });
}

static void CollectBlockClassVarDecls(
    const Stmt* s, const std::unordered_set<std::string_view>& class_names,
    std::unordered_map<std::string_view, std::string_view>& var_types) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl &&
      s->var_decl_type.kind == DataTypeKind::kNamed &&
      class_names.count(s->var_decl_type.type_name)) {
    var_types[s->var_name] = s->var_decl_type.type_name;
  }
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CollectBlockClassVarDecls(sub, class_names, var_types);
  });
}

void ElaboratorClassRules::ValidateLocalProtectedAccess(
    const ModuleDecl* decl) {
  if (class_names_.empty()) return;
  const AccessSite kOutside;
  for (const auto* item : decl->items) {
    CheckVarInitConstructorAccess(*item);
    bool is_proc = IsProceduralItemKind(item->kind);
    if (!is_proc || !item->body) continue;
    auto var_types = class_var_types_;
    CollectBlockClassVarDecls(item->body, class_names_, var_types);
    WalkStmtsForVisibility(item->body, var_types, kOutside, unit_, diag_);
  }
  WalkSubroutinesForVisibility(decl->items, {}, class_var_types_);
}

void ElaboratorClassRules::CheckVarInitConstructorAccess(
    const ModuleItem& item) {
  if (item.kind == ModuleItemKind::kVarDecl && IsBareNew(item.init_expr)) {
    CheckConstructorAccess(item.data_type.type_name, item.loc, AccessSite{},
                           unit_, diag_);
  }
}

void ElaboratorClassRules::WalkSubroutinesForVisibility(
    const std::vector<ModuleItem*>& items,
    const std::vector<const ClassDecl*>& classes,
    const std::unordered_map<std::string_view, std::string_view>& scope_types) {
  for (const SubroutineSite& sub : SubroutinesAmong(items, classes)) {
    AccessSite site{sub.inside, {}};
    if (!sub.inside.empty()) site.locals = CollectMethodLocalNames(sub.sub);
    auto var_types = scope_types;
    std::unordered_set<std::string_view> names;
    AddSubroutineHandles(sub, class_names_, unit_, names, var_types);
    for (const Stmt* s : sub.sub->func_body_stmts) {
      CollectBlockClassVarDecls(s, class_names_, var_types);
    }
    for (const Stmt* s : sub.sub->func_body_stmts) {
      WalkStmtsForVisibility(s, var_types, site, unit_, diag_);
    }
  }
}

void ElaboratorClassRules::ValidateLocalProtectedAccessOutsideModules() {
  for (const auto* item : unit_->cu_items) CheckVarInitConstructorAccess(*item);
  WalkSubroutinesForVisibility(
      unit_->cu_items, {unit_->classes.begin(), unit_->classes.end()}, {});
  for (const auto* pkg : unit_->packages) {
    for (const auto* item : pkg->items) CheckVarInitConstructorAccess(*item);
    WalkSubroutinesForVisibility(pkg->items, {}, {});
  }
}

static void CheckParamScopeExpr(
    const Expr* e, const std::unordered_set<std::string_view>& param_classes,
    DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess && e->lhs && e->rhs &&
      e->lhs->kind == ExprKind::kIdentifier && !e->lhs->has_param_spec &&
      param_classes.count(e->lhs->text)) {
    diag.Error(e->lhs->range.start,
               std::format("unadorned name '{}' used as scope resolution "
                           "prefix for parameterized class; use explicit "
                           "specialization '{}#(...)::' or '{}#()::'",
                           e->lhs->text, e->lhs->text, e->lhs->text),
               Subclause("8.25.1"));
  }
  CheckParamScopeExpr(e->lhs, param_classes, diag);
  CheckParamScopeExpr(e->rhs, param_classes, diag);
  CheckParamScopeExpr(e->base, param_classes, diag);
  CheckParamScopeExpr(e->index, param_classes, diag);
  CheckParamScopeExpr(e->condition, param_classes, diag);
  CheckParamScopeExpr(e->true_expr, param_classes, diag);
  CheckParamScopeExpr(e->false_expr, param_classes, diag);
  for (const auto* arg : e->args) CheckParamScopeExpr(arg, param_classes, diag);
}

static void WalkStmtsForParamScope(
    const Stmt* s, const std::unordered_set<std::string_view>& param_classes,
    DiagEngine& diag) {
  if (!s) return;
  CheckParamScopeExpr(s->lhs, param_classes, diag);
  CheckParamScopeExpr(s->rhs, param_classes, diag);
  CheckParamScopeExpr(s->expr, param_classes, diag);
  CheckParamScopeExpr(s->condition, param_classes, diag);
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkStmtsForParamScope(sub, param_classes, diag);
  });
}

void ElaboratorClassRules::ValidateParameterizedScopeResolution(
    const ModuleDecl* decl) {
  if (parameterized_class_names_.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckParamScopeExpr(item->assign_rhs, parameterized_class_names_, diag_);
    }
    CheckParamScopeExpr(item->init_expr, parameterized_class_names_, diag_);
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForParamScope(item->body, parameterized_class_names_, diag_);
    }
    CheckParamScopeInItem(*item);
  }
}

void ElaboratorClassRules::CheckParamScopeInItem(const ModuleItem& item) {
  if (item.kind == ModuleItemKind::kFunctionDecl ||
      item.kind == ModuleItemKind::kTaskDecl) {
    CheckParamScopeInSubroutine(item, {item.method_class});
  } else if (item.kind == ModuleItemKind::kClassDecl) {
    CheckParamScopeInClass(*item.class_decl, {});
  }
}

void ElaboratorClassRules::CheckParamScopeInSubroutine(
    const ModuleItem& sub,
    const std::unordered_set<std::string_view>& allowed) {
  std::unordered_set<std::string_view> checked;
  for (const std::string_view kName : parameterized_class_names_) {
    if (!allowed.contains(kName)) checked.insert(kName);
  }
  for (const Stmt* s : sub.func_body_stmts) {
    WalkStmtsForParamScope(s, checked, diag_);
  }
}

void ElaboratorClassRules::CheckParamScopeInClass(
    const ClassDecl& cls, std::unordered_set<std::string_view> allowed) {
  allowed.insert(cls.name);
  for (const ClassMember* m : cls.members) {
    if (m->method != nullptr) CheckParamScopeInSubroutine(*m->method, allowed);
    if (m->nested_class != nullptr) {
      CheckParamScopeInClass(*m->nested_class, allowed);
    }
  }
}

void ElaboratorClassRules::ValidateParameterizedScopeOutsideModules() {
  if (parameterized_class_names_.empty()) return;
  std::vector<const std::vector<ModuleItem*>*> scopes{&unit_->cu_items};
  for (const auto* pkg : unit_->packages) scopes.push_back(&pkg->items);
  for (const auto* items : scopes) {
    for (const auto* item : *items) {
      CheckParamScopeExpr(item->init_expr, parameterized_class_names_, diag_);
      CheckParamScopeInItem(*item);
    }
  }
  for (const auto* cls : unit_->classes) CheckParamScopeInClass(*cls, {});
}

namespace {

struct RestrictedScopePrefixes {
  std::unordered_set<std::string_view> incomplete_forward_types;
  std::unordered_set<std::string_view> interface_based_typedefs;

  bool Empty() const {
    return incomplete_forward_types.empty() && interface_based_typedefs.empty();
  }
};

}  // namespace

static void ReportRestrictedScopePrefix(std::string_view name, SourceLoc loc,
                                        const RestrictedScopePrefixes& r,
                                        DiagEngine& diag) {
  if (name.empty()) return;
  if (r.incomplete_forward_types.count(name)) {
    diag.Error(loc,
               std::format("incomplete forward type '{}' {}", name,
                           kPermittedScopePrefixContexts),
               Subclause("8.23"));
  } else if (r.interface_based_typedefs.count(name)) {
    diag.Error(loc,
               std::format("type '{}' defined by an interface-based typedef {}",
                           name, kPermittedScopePrefixContexts),
               Subclause("8.23"));
  }
}

static void CheckRestrictedScopePrefixExpr(const Expr* e,
                                           const RestrictedScopePrefixes& r,
                                           DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess && e->is_scope_resolution && e->lhs &&
      e->rhs && e->lhs->kind == ExprKind::kIdentifier) {
    ReportRestrictedScopePrefix(e->lhs->text, e->lhs->range.start, r, diag);
  }
  CheckRestrictedScopePrefixExpr(e->lhs, r, diag);
  CheckRestrictedScopePrefixExpr(e->rhs, r, diag);
  CheckRestrictedScopePrefixExpr(e->base, r, diag);
  CheckRestrictedScopePrefixExpr(e->index, r, diag);
  CheckRestrictedScopePrefixExpr(e->condition, r, diag);
  CheckRestrictedScopePrefixExpr(e->true_expr, r, diag);
  CheckRestrictedScopePrefixExpr(e->false_expr, r, diag);
  for (const auto* arg : e->args) CheckRestrictedScopePrefixExpr(arg, r, diag);
}

static void WalkStmtsForRestrictedScopePrefix(const Stmt* s,
                                              const RestrictedScopePrefixes& r,
                                              DiagEngine& diag) {
  if (!s) return;
  CheckRestrictedScopePrefixExpr(s->lhs, r, diag);
  CheckRestrictedScopePrefixExpr(s->rhs, r, diag);
  CheckRestrictedScopePrefixExpr(s->expr, r, diag);
  CheckRestrictedScopePrefixExpr(s->condition, r, diag);
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    WalkStmtsForRestrictedScopePrefix(sub, r, diag);
  });
}

static void CollectScopePrefixTypedefs(
    const std::vector<ModuleItem*>& items, RestrictedScopePrefixes& r,
    std::unordered_set<std::string_view>& completed_forward_types) {
  for (const auto* item : items) {
    if (item->kind != ModuleItemKind::kTypedef) continue;
    if (!item->typedef_ifc_port.empty()) {
      r.interface_based_typedefs.insert(item->name);
    } else if (item->typedef_type.kind == DataTypeKind::kImplicit) {
      r.incomplete_forward_types.insert(item->name);
    } else {
      completed_forward_types.insert(item->name);
    }
  }
}

static void DropCompletedForwardTypes(
    RestrictedScopePrefixes& r,
    const std::unordered_set<std::string_view>& completed_forward_types,
    const std::unordered_set<std::string_view>& class_names) {
  std::erase_if(r.incomplete_forward_types, [&](std::string_view name) {
    return completed_forward_types.count(name) > 0 ||
           class_names.count(name) > 0;
  });
}

static RestrictedScopePrefixes CollectModuleRestrictedPrefixes(
    const ModuleDecl* decl, const CompilationUnit* unit,
    const std::unordered_set<std::string_view>& class_names) {
  RestrictedScopePrefixes r;
  std::unordered_set<std::string_view> completed_forward_types;
  CollectScopePrefixTypedefs(decl->items, r, completed_forward_types);
  CollectScopePrefixTypedefs(unit->cu_items, r, completed_forward_types);
  DropCompletedForwardTypes(r, completed_forward_types, class_names);
  return r;
}

static void CheckClassPropertyScopePrefixes(const ClassDecl* cls,
                                            const RestrictedScopePrefixes& r,
                                            DiagEngine& diag) {
  for (const auto* member : cls->members) {
    if (member->kind == ClassMemberKind::kProperty && !member->is_param) {
      ReportRestrictedScopePrefix(member->data_type.scope_name, member->loc, r,
                                  diag);
    }
    if (member->kind == ClassMemberKind::kClassDecl && member->nested_class) {
      CheckClassPropertyScopePrefixes(member->nested_class, r, diag);
    }
  }
}

static void CheckItemForRestrictedScopePrefix(const ModuleItem* item,
                                              const RestrictedScopePrefixes& r,
                                              DiagEngine& diag) {
  if (item->kind == ModuleItemKind::kVarDecl) {
    ReportRestrictedScopePrefix(item->data_type.scope_name, item->loc, r, diag);
    return;
  }
  if (item->kind == ModuleItemKind::kClassDecl && item->class_decl) {
    CheckClassPropertyScopePrefixes(item->class_decl, r, diag);
    return;
  }
  if (item->kind == ModuleItemKind::kContAssign) {
    CheckRestrictedScopePrefixExpr(item->assign_lhs, r, diag);
    CheckRestrictedScopePrefixExpr(item->assign_rhs, r, diag);
    return;
  }
  bool is_proc = IsProceduralItemKind(item->kind);
  if (is_proc && item->body) {
    WalkStmtsForRestrictedScopePrefix(item->body, r, diag);
  }
}

void ElaboratorClassRules::ValidateRestrictedScopePrefixUsage(
    const ModuleDecl* decl) {
  RestrictedScopePrefixes restricted =
      CollectModuleRestrictedPrefixes(decl, unit_, class_names_);
  if (restricted.Empty()) return;
  for (const auto* item : decl->items) {
    CheckItemForRestrictedScopePrefix(item, restricted, diag_);
  }
}

void ElaboratorClassRules::ValidateRestrictedScopePrefixInClasses() {
  for (const auto* cls : unit_->classes) {
    RestrictedScopePrefixes restricted;
    std::unordered_set<std::string_view> completed_forward_types;
    CollectScopePrefixTypedefs(unit_->cu_items, restricted,
                               completed_forward_types);
    DropCompletedForwardTypes(restricted, completed_forward_types,
                              class_names_);
    if (restricted.Empty()) continue;
    CheckClassPropertyScopePrefixes(cls, restricted, diag_);
  }
}

static bool ForwardClassTypedefIsResolved(const ModuleItem* item,
                                          const CompilationUnit* unit) {
  for (const auto* cls : unit->classes) {
    if (cls->name == item->name) return true;
  }
  for (const auto* other : unit->cu_items) {
    if (other == item) continue;
    if (other->kind == ModuleItemKind::kTypedef && other->name == item->name &&
        other->typedef_type.kind != DataTypeKind::kImplicit) {
      return true;
    }
  }
  return false;
}

void ElaboratorClassRules::ValidateForwardClassTypedefs() {
  for (const auto* item : unit_->cu_items) {
    if (item->kind != ModuleItemKind::kTypedef) continue;
    if (item->typedef_type.kind != DataTypeKind::kImplicit) continue;
    if (!ForwardClassTypedefIsResolved(item, unit_)) {
      diag_.Error(item->loc,
                  std::format("forward typedef '{}' is never resolved by a "
                              "definition in the same scope",
                              item->name),
                  Subclause("6.18"));
    }
  }
}

}  // namespace delta
