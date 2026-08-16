#include <format>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

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
    // §8.5 states this rule and gives this construct as its example:
    // "Accessing data types using a class handle is not allowed." §8.23
    // defines the `::` operator, which is the legal alternative rather than
    // the rule being broken.
    diag.Error(e->rhs->range.start,
               "cannot access type parameter via class handle",
               Subclause("8.5"));
    return;
  }
  const auto* m = FindMemberInClass(cls, e->rhs->text, unit);
  if (m && m->is_local) {
    diag.Error(e->rhs->range.start,
               "cannot access local member from outside its class",
               Subclause("8.18"));
  } else if (m && m->is_protected) {
    diag.Error(e->rhs->range.start,
               "cannot access protected member from outside "
               "its class hierarchy",
               Subclause("8.18"));
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
  // §18.11 states this rule: "The random mode of local class members can only
  // be changed when the call to randomize() has access to those properties,
  // that is, within the scope of the class in which the local members are
  // declared." §8.18 states the general rule that a local or protected member
  // is unreachable from outside, which CheckMemberAccessVisibility enforces.
  // What is rejected here is a change of random mode rather than a read.
  const auto* m = FindMemberInClass(cls, arg->text, unit);
  if (m && m->is_local) {
    diag.Error(arg->range.start,
               "cannot change random mode of local member from outside "
               "its class",
               Subclause("18.11"));
  } else if (m && m->is_protected) {
    diag.Error(arg->range.start,
               "cannot change random mode of protected member from "
               "outside its class hierarchy",
               Subclause("18.11"));
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
    bool is_proc = IsProceduralItemKind(item->kind);
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
            std::format("assignment to global constant '{}'", s->lhs->text),
            Subclause("8.19"));
      } else if (instance_consts.count(s->lhs->text) && !in_constructor) {
        diag.Error(
            s->range.start,
            std::format(
                "assignment to instance constant '{}' outside constructor",
                s->lhs->text),
            Subclause("8.19"));
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
      diag.Error(m->loc, "instance constant cannot be declared static",
                 Subclause("8.19"));
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
                             s->lhs->text),
                 Subclause("8.19"));
    }
  }
}

// §8.10: check one class method for writes to a const class property. A class
// subroutine body is stored in func_body_stmts, not the single `body` statement
// used by module procedural blocks, so each statement is walked. Only the
// constructor may write an instance const, and only once.
static void CheckConstClassPropsInMethod(
    const ModuleItem* method,
    const std::unordered_set<std::string_view>& global_consts,
    const std::unordered_set<std::string_view>& instance_consts,
    DiagEngine& diag) {
  bool is_ctor = method->name == "new";
  for (const auto* s : method->func_body_stmts) {
    WalkStmtsForConstClassProp(s, global_consts, instance_consts, is_ctor,
                               diag);
  }
  if (is_ctor) CheckInstanceConstSingleAssign(method, instance_consts, diag);
}

void Elaborator::ValidateConstClassProperties() {
  for (const auto* cls : unit_->classes) {
    std::unordered_set<std::string_view> global_consts;
    std::unordered_set<std::string_view> instance_consts;
    CollectConstClassProperties(cls, global_consts, instance_consts, diag_);
    if (global_consts.empty() && instance_consts.empty()) continue;
    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
      CheckConstClassPropsInMethod(m->method, global_consts, instance_consts,
                                   diag_);
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
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForParamScope(item->body, parameterized_class_names_, diag_);
    }
  }
}

namespace {

// §8.23 names three kinds of prefix that may resolve to a class type without
// naming a class outright: an incomplete forward type, a type defined by an
// interface-based typedef (§6.18), and a type parameter (§6.20.3). The
// subclause states one restriction for all three, so one set per kind carries
// the names each restriction applies to.
struct RestrictedScopePrefixes {
  std::unordered_set<std::string_view> incomplete_forward_types;
  std::unordered_set<std::string_view> interface_based_typedefs;
  std::unordered_set<std::string_view> type_params;

  bool Empty() const {
    return incomplete_forward_types.empty() &&
           interface_based_typedefs.empty() && type_params.empty();
  }
};

// The three contexts §8.23 permits, written once because the subclause states
// them once for every prefix kind it restricts.
constexpr std::string_view kPermittedScopePrefixContexts =
    "may prefix the class scope resolution operator only within a typedef "
    "declaration, the type operator, or a type parameter assignment";

}  // namespace

// §8.23 restricts the use of the class scope resolution operator to select a
// type through any of its three prefix kinds to typedef declarations, the type
// operator, and type parameter assignments. §6.20.3 states the type-parameter
// case in its own words and carries the example the rule is usually met
// through, so that leg is reported there; the other two kinds are stated by
// §8.23 alone. `name` is the prefix written before the operator and `loc` is
// where the expression or the declaration carrying it is reported.
static void ReportRestrictedScopePrefix(std::string_view name, SourceLoc loc,
                                        const RestrictedScopePrefixes& r,
                                        DiagEngine& diag) {
  if (name.empty()) return;
  if (r.type_params.count(name)) {
    diag.Error(loc,
               std::format("type parameter '{}' {}", name,
                           kPermittedScopePrefixContexts),
               Subclause("6.20.3"));
  } else if (r.incomplete_forward_types.count(name)) {
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

// The three contexts §8.23 permits are parsed as data types (carrying a
// scope_name), never as expressions, so a prefix that surfaces in an expression
// is outside the permitted set by construction.
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
  for (auto* sub : s->stmts) WalkStmtsForRestrictedScopePrefix(sub, r, diag);
  WalkStmtsForRestrictedScopePrefix(s->then_branch, r, diag);
  WalkStmtsForRestrictedScopePrefix(s->else_branch, r, diag);
  WalkStmtsForRestrictedScopePrefix(s->body, r, diag);
  WalkStmtsForRestrictedScopePrefix(s->for_body, r, diag);
  for (auto& ci : s->case_items)
    WalkStmtsForRestrictedScopePrefix(ci.body, r, diag);
}

// Sorts the typedefs of one scope into the kinds §8.23 restricts, and collects
// the names of the typedefs that give a forward declaration its definition.
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

// §6.18 makes a forward type declaration legal either before or after the
// definition that resolves it, so a resolved name is a complete type at every
// use; only an unresolved name is the incomplete forward type §8.23 restricts.
static void DropCompletedForwardTypes(
    RestrictedScopePrefixes& r,
    const std::unordered_set<std::string_view>& completed_forward_types,
    const std::unordered_set<std::string_view>& class_names) {
  std::erase_if(r.incomplete_forward_types, [&](std::string_view name) {
    return completed_forward_types.count(name) > 0 ||
           class_names.count(name) > 0;
  });
}

// Collects the prefixes §8.23 restricts in one module scope. Type parameters
// come from the parameter port list (recorded by the parser) and from body
// declarations, where a `parameter type`/`localparam type` item is carried as a
// parameter declaration whose data type is void.
static RestrictedScopePrefixes CollectModuleRestrictedPrefixes(
    const ModuleDecl* decl, const CompilationUnit* unit,
    const std::unordered_set<std::string_view>& class_names) {
  RestrictedScopePrefixes r;
  r.type_params = decl->type_param_names;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kParamDecl &&
        item->data_type.kind == DataTypeKind::kVoid) {
      r.type_params.insert(item->name);
    }
  }
  std::unordered_set<std::string_view> completed_forward_types;
  CollectScopePrefixTypedefs(decl->items, r, completed_forward_types);
  CollectScopePrefixTypedefs(unit->cu_items, r, completed_forward_types);
  DropCompletedForwardTypes(r, completed_forward_types, class_names);
  return r;
}

// §6.20.3's illegal example is a class property, `C::T x;` in the body of
// `class P#(type C)`. A property declaration is none of the three contexts
// §8.23 permits, so the prefix on its declared type is reported. A member
// carrying is_param is a parameter declaration and a kTypedef member is a
// typedef declaration, which are two of the contexts the subclause permits, so
// neither is examined. A nested class sees the type parameters of the class it
// is declared in as well as its own.
static void CheckClassPropertyScopePrefixes(const ClassDecl* cls,
                                            const RestrictedScopePrefixes& r,
                                            DiagEngine& diag) {
  for (const auto* member : cls->members) {
    if (member->kind == ClassMemberKind::kProperty && !member->is_param) {
      ReportRestrictedScopePrefix(member->data_type.scope_name, member->loc, r,
                                  diag);
    }
    if (member->kind == ClassMemberKind::kClassDecl && member->nested_class) {
      RestrictedScopePrefixes nested = r;
      nested.type_params.insert(member->nested_class->type_param_names.begin(),
                                member->nested_class->type_param_names.end());
      CheckClassPropertyScopePrefixes(member->nested_class, nested, diag);
    }
  }
}

// Checks one module item for a restricted prefix, in whichever of the two
// positions that item kind can carry one: the declared data type of a variable
// declaration or a class property, or an expression.
static void CheckItemForRestrictedScopePrefix(const ModuleItem* item,
                                              const RestrictedScopePrefixes& r,
                                              DiagEngine& diag) {
  if (item->kind == ModuleItemKind::kVarDecl) {
    ReportRestrictedScopePrefix(item->data_type.scope_name, item->loc, r, diag);
    return;
  }
  if (item->kind == ModuleItemKind::kClassDecl && item->class_decl) {
    RestrictedScopePrefixes in_class = r;
    in_class.type_params.insert(item->class_decl->type_param_names.begin(),
                                item->class_decl->type_param_names.end());
    CheckClassPropertyScopePrefixes(item->class_decl, in_class, diag);
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

void Elaborator::ValidateRestrictedScopePrefixUsage(const ModuleDecl* decl) {
  RestrictedScopePrefixes restricted =
      CollectModuleRestrictedPrefixes(decl, unit_, class_names_);
  if (restricted.Empty()) return;
  for (const auto* item : decl->items) {
    CheckItemForRestrictedScopePrefix(item, restricted, diag_);
  }
}

void Elaborator::ValidateRestrictedScopePrefixInClasses() {
  for (const auto* cls : unit_->classes) {
    RestrictedScopePrefixes restricted;
    restricted.type_params = cls->type_param_names;
    // The scope enclosing a class declared at the outermost level is the
    // compilation unit, so the forward types and interface-based typedefs it
    // can name as a prefix are the ones declared there.
    std::unordered_set<std::string_view> completed_forward_types;
    CollectScopePrefixTypedefs(unit_->cu_items, restricted,
                               completed_forward_types);
    DropCompletedForwardTypes(restricted, completed_forward_types,
                              class_names_);
    if (restricted.Empty()) continue;
    CheckClassPropertyScopePrefixes(cls, restricted, diag_);
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

// The type a module item declares through a named type, or null for an item
// that declares none. A typedef declaration and a type parameter assignment
// both hold the type they bind in typedef_type, the latter on a parameter
// declaration whose own data type is void; a variable declaration holds its
// type in data_type. The parser records a scope prefix on all three.
static const DataType* DeclaredNamedType(const ModuleItem* item) {
  bool binds_typedef_type = item->kind == ModuleItemKind::kTypedef ||
                            (item->kind == ModuleItemKind::kParamDecl &&
                             item->data_type.kind == DataTypeKind::kVoid);
  const DataType* declared = nullptr;
  if (binds_typedef_type) {
    declared = &item->typedef_type;
  } else if (item->kind == ModuleItemKind::kVarDecl) {
    declared = &item->data_type;
  }
  if (!declared || declared->kind != DataTypeKind::kNamed) return nullptr;
  return declared;
}

// Checks one item whose named type carries a scope prefix: if that prefix names
// a body type parameter bound to a type that is definitely not a class (any
// non-named type), report the error.
static void CheckItemScopePrefixResolvesToClass(
    const ModuleItem* item,
    const std::unordered_map<std::string_view, const DataType*>&
        type_param_bound,
    DiagEngine& diag) {
  const DataType* declared = DeclaredNamedType(item);
  if (!declared) return;
  auto scope = declared->scope_name;
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
                           scope),
               Subclause("6.20.3"));
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
    CheckItemScopePrefixResolvesToClass(item, type_param_bound, diag_);
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
                              item->name),
                  // §6.18 is the rule: "The actual data type definition of a
                  // forward typedef declaration shall be resolved within the
                  // same local scope or generate block." §8.27 restates it for
                  // a forward class declaration and says so, opening "As with
                  // other forward typedefs as described in 6.18". This loop
                  // selects every forward form Parser::ParseTypedef leaves
                  // implicit, a forward struct and a bare typedef included, so
                  // §6.18 is the only clause covering what it reports.
                  Subclause("6.18"));
    }
  }
}

}  // namespace delta
