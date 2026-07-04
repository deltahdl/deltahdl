#include <format>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

static const ClassMember* FindMemberInClass(const ClassDecl* cls,
                                            std::string_view name,
                                            const CompilationUnit* unit) {
  for (const auto* c = cls; c;) {
    for (const auto* m : c->members) {
      if (m->name == name) return m;
      // §8.18: a method member carries its name on the method item, not on the
      // ClassMember, so match that too — the local/protected qualifiers live on
      // the ClassMember and must govern method calls just as for data members.
      if (m->method != nullptr && m->method->name == name) return m;
    }
    if (c->base_class.empty()) break;
    c = FindClassDecl(c->base_class, unit);
  }
  return nullptr;
}

static void CheckMemberAccessVisibility(
    const Expr* e,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  if (e->lhs->kind != ExprKind::kIdentifier) return;
  auto it = var_types.find(e->lhs->text);
  if (it == var_types.end()) return;
  if (e->rhs->kind != ExprKind::kIdentifier) return;
  const auto* cls = FindClassDecl(it->second, unit);
  if (!cls) return;

  if (cls->type_param_names.count(e->rhs->text) > 0) {
    diag.Error(e->rhs->range.start,
               "cannot access type parameter via class handle");
    return;
  }
  const auto* m = FindMemberInClass(cls, e->rhs->text, unit);
  if (m && m->is_local) {
    diag.Error(e->rhs->range.start,
               "cannot access local member from outside its class");
  } else if (m && m->is_protected) {
    diag.Error(e->rhs->range.start,
               "cannot access protected member from outside "
               "its class hierarchy");
  }
}

// 18.11: naming a property in randomize()'s inline argument list changes that
// property's random mode. The random mode of a local or protected member may
// only be changed where the caller can reach that member. When randomize() is
// invoked through an external class handle, its arguments name members of that
// handle's class, so the same visibility rule that governs an obj.member access
// applies to each argument here.
static void CheckRandomizeArgItemVisibility(const Expr* arg,
                                            const ClassDecl* cls,
                                            const CompilationUnit* unit,
                                            DiagEngine& diag) {
  if (!arg || arg->kind != ExprKind::kIdentifier) return;
  const auto* m = FindMemberInClass(cls, arg->text, unit);
  if (m && m->is_local) {
    diag.Error(arg->range.start,
               "cannot change random mode of local member from outside "
               "its class");
  } else if (m && m->is_protected) {
    diag.Error(arg->range.start,
               "cannot change random mode of protected member from "
               "outside its class hierarchy");
  }
}

static void CheckRandomizeArgVisibility(
    const Expr* e,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
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
    CheckRandomizeArgItemVisibility(arg, cls, unit, diag);
  }
}

static void CheckVisibilityExpr(
    const Expr* e,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess && e->lhs && e->rhs) {
    CheckMemberAccessVisibility(e, var_types, unit, diag);
  }
  if (e->kind == ExprKind::kCall) {
    CheckRandomizeArgVisibility(e, var_types, unit, diag);
  }
  CheckVisibilityExpr(e->lhs, var_types, unit, diag);
  CheckVisibilityExpr(e->rhs, var_types, unit, diag);
  CheckVisibilityExpr(e->base, var_types, unit, diag);
  CheckVisibilityExpr(e->index, var_types, unit, diag);
  CheckVisibilityExpr(e->condition, var_types, unit, diag);
  CheckVisibilityExpr(e->true_expr, var_types, unit, diag);
  CheckVisibilityExpr(e->false_expr, var_types, unit, diag);
  for (const auto* arg : e->args)
    CheckVisibilityExpr(arg, var_types, unit, diag);
}

static void WalkStmtsForVisibility(
    const Stmt* s,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  if (!s) return;
  CheckVisibilityExpr(s->lhs, var_types, unit, diag);
  CheckVisibilityExpr(s->rhs, var_types, unit, diag);
  CheckVisibilityExpr(s->expr, var_types, unit, diag);
  CheckVisibilityExpr(s->condition, var_types, unit, diag);
  for (auto* sub : s->stmts) WalkStmtsForVisibility(sub, var_types, unit, diag);
  WalkStmtsForVisibility(s->then_branch, var_types, unit, diag);
  WalkStmtsForVisibility(s->else_branch, var_types, unit, diag);
  WalkStmtsForVisibility(s->body, var_types, unit, diag);
  WalkStmtsForVisibility(s->for_body, var_types, unit, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForVisibility(ci.body, var_types, unit, diag);
}

// §8.18: collect class-typed handle variables declared inside a procedural
// block. These block-local handles are not recorded in class_var_types_ (which
// is seeded only from module-scope handles), yet member accesses through them
// are still subject to the local/protected visibility rules.
static void CollectBlockClassVarDecls(
    const Stmt* s, const std::unordered_set<std::string_view>& class_names,
    std::unordered_map<std::string_view, std::string_view>& var_types) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl &&
      s->var_decl_type.kind == DataTypeKind::kNamed &&
      class_names.count(s->var_decl_type.type_name)) {
    var_types[s->var_name] = s->var_decl_type.type_name;
  }
  for (auto* sub : s->stmts)
    CollectBlockClassVarDecls(sub, class_names, var_types);
  CollectBlockClassVarDecls(s->then_branch, class_names, var_types);
  CollectBlockClassVarDecls(s->else_branch, class_names, var_types);
  CollectBlockClassVarDecls(s->body, class_names, var_types);
  CollectBlockClassVarDecls(s->for_body, class_names, var_types);
  for (auto& ci : s->case_items)
    CollectBlockClassVarDecls(ci.body, class_names, var_types);
}

void Elaborator::ValidateLocalProtectedAccess(const ModuleDecl* decl) {
  if (class_names_.empty()) return;
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (!is_proc || !item->body) continue;
    // Combine module-scope handles with any declared inside this block.
    auto var_types = class_var_types_;
    CollectBlockClassVarDecls(item->body, class_names_, var_types);
    WalkStmtsForVisibility(item->body, var_types, unit_, diag_);
  }
}

static void WalkStmtsForConstClassProp(
    const Stmt* s, const std::unordered_set<std::string_view>& global_consts,
    const std::unordered_set<std::string_view>& instance_consts,
    bool in_constructor, DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    if (s->lhs && s->lhs->kind == ExprKind::kIdentifier) {
      if (global_consts.count(s->lhs->text)) {
        diag.Error(
            s->range.start,
            std::format("assignment to global constant '{}'", s->lhs->text));
      } else if (instance_consts.count(s->lhs->text) && !in_constructor) {
        diag.Error(
            s->range.start,
            std::format(
                "assignment to instance constant '{}' outside constructor",
                s->lhs->text));
      }
    }
  }
  for (auto* sub : s->stmts)
    WalkStmtsForConstClassProp(sub, global_consts, instance_consts,
                               in_constructor, diag);
  WalkStmtsForConstClassProp(s->then_branch, global_consts, instance_consts,
                             in_constructor, diag);
  WalkStmtsForConstClassProp(s->else_branch, global_consts, instance_consts,
                             in_constructor, diag);
  WalkStmtsForConstClassProp(s->body, global_consts, instance_consts,
                             in_constructor, diag);
  WalkStmtsForConstClassProp(s->for_body, global_consts, instance_consts,
                             in_constructor, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForConstClassProp(ci.body, global_consts, instance_consts,
                               in_constructor, diag);
}

static void CollectConstClassProperties(
    const ClassDecl* cls, std::unordered_set<std::string_view>& global_consts,
    std::unordered_set<std::string_view>& instance_consts, DiagEngine& diag) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kProperty || !m->is_const) continue;
    if (!m->init_expr && m->is_static) {
      diag.Error(m->loc, "instance constant cannot be declared static");
    }
    if (m->init_expr) {
      global_consts.insert(m->name);
    } else {
      instance_consts.insert(m->name);
    }
  }
}

// §8.19: an instance constant may be assigned in the constructor, but the
// assignment can only be done once. Two unconditional writes at the top level
// of new() are an unambiguous double assignment. Only top-level statements are
// counted so a value chosen across the branches of an if/else (a single
// dynamic write) is not mistaken for two writes.
static void CheckInstanceConstSingleAssign(
    const ModuleItem* ctor,
    const std::unordered_set<std::string_view>& instance_consts,
    DiagEngine& diag) {
  std::unordered_map<std::string_view, int> counts;
  for (const auto* s : ctor->func_body_stmts) {
    if (!s) continue;
    if (s->kind != StmtKind::kBlockingAssign &&
        s->kind != StmtKind::kNonblockingAssign)
      continue;
    if (!s->lhs || s->lhs->kind != ExprKind::kIdentifier) continue;
    if (!instance_consts.count(s->lhs->text)) continue;
    if (++counts[s->lhs->text] == 2) {
      diag.Error(s->range.start,
                 std::format("instance constant '{}' is assigned more than "
                             "once in the constructor",
                             s->lhs->text));
    }
  }
}

void Elaborator::ValidateConstClassProperties() {
  for (const auto* cls : unit_->classes) {
    std::unordered_set<std::string_view> global_consts;
    std::unordered_set<std::string_view> instance_consts;
    CollectConstClassProperties(cls, global_consts, instance_consts, diag_);
    if (global_consts.empty() && instance_consts.empty()) continue;
    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
      bool is_ctor = m->method->name == "new";
      // A class subroutine body is stored in func_body_stmts, not the single
      // `body` statement used by module procedural blocks; walk each statement
      // so const-property assignments inside methods/tasks are actually
      // checked.
      for (const auto* s : m->method->func_body_stmts) {
        WalkStmtsForConstClassProp(s, global_consts, instance_consts, is_ctor,
                                   diag_);
      }
      if (is_ctor)
        CheckInstanceConstSingleAssign(m->method, instance_consts, diag_);
    }
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
                           e->lhs->text, e->lhs->text, e->lhs->text));
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
  for (auto* sub : s->stmts) WalkStmtsForParamScope(sub, param_classes, diag);
  WalkStmtsForParamScope(s->then_branch, param_classes, diag);
  WalkStmtsForParamScope(s->else_branch, param_classes, diag);
  WalkStmtsForParamScope(s->body, param_classes, diag);
  WalkStmtsForParamScope(s->for_body, param_classes, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForParamScope(ci.body, param_classes, diag);
}

void Elaborator::ValidateParameterizedScopeResolution(const ModuleDecl* decl) {
  if (parameterized_class_names_.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckParamScopeExpr(item->assign_rhs, parameterized_class_names_, diag_);
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      WalkStmtsForParamScope(item->body, parameterized_class_names_, diag_);
    }
  }
}

// §6.20.3 and §8.23 both state the same restriction: while a type parameter
// may resolve to a class type, using it as the prefix of the class scope
// resolution operator '::' is restricted to typedef declarations, the type
// operator, and type parameter assignments. Those three contexts are parsed as
// data types (carrying a scope_name), never as expressions, so a type
// parameter that surfaces as the prefix of a member-access expression is always
// outside the permitted set. Both subclauses agree on this rule; enforcing it
// from one place keeps them consistent.
static void CheckTypeParamScopeExpr(
    const Expr* e, const std::unordered_set<std::string_view>& type_params,
    DiagEngine& diag) {
  if (!e) return;
  if (e->kind == ExprKind::kMemberAccess && e->lhs && e->rhs &&
      e->lhs->kind == ExprKind::kIdentifier &&
      type_params.count(e->lhs->text)) {
    diag.Error(e->lhs->range.start,
               std::format("type parameter '{}' may prefix the class scope "
                           "resolution operator only within a typedef "
                           "declaration, the type operator, or a type "
                           "parameter assignment",
                           e->lhs->text));
  }
  CheckTypeParamScopeExpr(e->lhs, type_params, diag);
  CheckTypeParamScopeExpr(e->rhs, type_params, diag);
  CheckTypeParamScopeExpr(e->base, type_params, diag);
  CheckTypeParamScopeExpr(e->index, type_params, diag);
  CheckTypeParamScopeExpr(e->condition, type_params, diag);
  CheckTypeParamScopeExpr(e->true_expr, type_params, diag);
  CheckTypeParamScopeExpr(e->false_expr, type_params, diag);
  for (const auto* arg : e->args)
    CheckTypeParamScopeExpr(arg, type_params, diag);
}

static void WalkStmtsForTypeParamScope(
    const Stmt* s, const std::unordered_set<std::string_view>& type_params,
    DiagEngine& diag) {
  if (!s) return;
  CheckTypeParamScopeExpr(s->lhs, type_params, diag);
  CheckTypeParamScopeExpr(s->rhs, type_params, diag);
  CheckTypeParamScopeExpr(s->expr, type_params, diag);
  CheckTypeParamScopeExpr(s->condition, type_params, diag);
  for (auto* sub : s->stmts) WalkStmtsForTypeParamScope(sub, type_params, diag);
  WalkStmtsForTypeParamScope(s->then_branch, type_params, diag);
  WalkStmtsForTypeParamScope(s->else_branch, type_params, diag);
  WalkStmtsForTypeParamScope(s->body, type_params, diag);
  WalkStmtsForTypeParamScope(s->for_body, type_params, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForTypeParamScope(ci.body, type_params, diag);
}

void Elaborator::ValidateTypeParamScopeUsage(const ModuleDecl* decl) {
  // Type parameters come from the parameter port list (recorded by the parser)
  // and from body declarations, where a `parameter type`/`localparam type`
  // item is carried as a parameter declaration whose data type is void.
  std::unordered_set<std::string_view> type_params = decl->type_param_names;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kParamDecl &&
        item->data_type.kind == DataTypeKind::kVoid) {
      type_params.insert(item->name);
    }
  }
  if (type_params.empty()) return;

  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kContAssign) {
      CheckTypeParamScopeExpr(item->assign_lhs, type_params, diag_);
      CheckTypeParamScopeExpr(item->assign_rhs, type_params, diag_);
    }
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kAlwaysCombBlock ||
                   item->kind == ModuleItemKind::kAlwaysFFBlock ||
                   item->kind == ModuleItemKind::kAlwaysLatchBlock ||
                   item->kind == ModuleItemKind::kInitialBlock ||
                   item->kind == ModuleItemKind::kFinalBlock;
    if (is_proc && item->body) {
      WalkStmtsForTypeParamScope(item->body, type_params, diag_);
    }
  }
}

// Collects each body type parameter and the type it is bound to.
static void CollectBoundTypeParams(
    const ModuleDecl* decl,
    std::unordered_map<std::string_view, const DataType*>& type_param_bound) {
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kParamDecl &&
        item->data_type.kind == DataTypeKind::kVoid &&
        item->typedef_type.kind != DataTypeKind::kImplicit) {
      type_param_bound[item->name] = &item->typedef_type;
    }
  }
}

// Checks one typedef whose named type carries a scope prefix: if that prefix
// names a body type parameter bound to a type that is definitely not a class
// (any non-named type), report the error.
static void CheckTypedefScopePrefixResolvesToClass(
    const ModuleItem* item,
    const std::unordered_map<std::string_view, const DataType*>&
        type_param_bound,
    DiagEngine& diag) {
  if (item->kind != ModuleItemKind::kTypedef) return;
  if (item->typedef_type.kind != DataTypeKind::kNamed) return;
  auto scope = item->typedef_type.scope_name;
  if (scope.empty()) return;
  auto it = type_param_bound.find(scope);
  if (it == type_param_bound.end()) return;
  // A built-in or otherwise non-named type can never be a class; a named type
  // is left alone (it may name a class, possibly one declared elsewhere) to
  // avoid false positives.
  if (it->second->kind != DataTypeKind::kNamed) {
    diag.Error(item->loc,
               std::format("type parameter '{}' used as a class scope "
                           "resolution prefix does not resolve to a class",
                           scope));
  }
}

void Elaborator::ValidateTypeParamScopePrefixResolvesToClass(
    const ModuleDecl* decl) {
  // §6.20.3: a type parameter may prefix the class scope resolution operator in
  // an allowed context (such as a typedef declaration) only when it resolves to
  // a class type; it shall be an error if the prefix does not resolve to a
  // class.
  std::unordered_map<std::string_view, const DataType*> type_param_bound;
  CollectBoundTypeParams(decl, type_param_bound);
  if (type_param_bound.empty()) return;

  for (const auto* item : decl->items) {
    CheckTypedefScopePrefixResolvesToClass(item, type_param_bound, diag_);
  }
}

// A forward typedef is resolved if a class of the same name exists, or another
// non-forward typedef in the same scope shares its name.
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

void Elaborator::ValidateForwardClassTypedefs() {
  for (const auto* item : unit_->cu_items) {
    if (item->kind != ModuleItemKind::kTypedef) continue;
    if (item->typedef_type.kind != DataTypeKind::kImplicit) continue;
    if (!ForwardClassTypedefIsResolved(item, unit_)) {
      diag_.Error(item->loc,
                  std::format("forward typedef '{}' is never resolved by a "
                              "definition in the same scope",
                              item->name));
    }
  }
}

}  // namespace delta
