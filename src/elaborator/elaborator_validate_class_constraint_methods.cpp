#include <format>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_class_constraints.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

static const ModuleItem* FindClassFunction(const ClassDecl* cls,
                                           std::string_view name,
                                           const CompilationUnit* unit) {
  for (const auto* c = cls; c; c = FindBaseClass(c, unit)) {
    for (const auto* m : c->members) {
      if (m->kind == ClassMemberKind::kMethod && m->method &&
          m->method->kind == ModuleItemKind::kFunctionDecl &&
          m->method->name == name) {
        return m->method;
      }
    }
  }
  return nullptr;
}

static bool IsModeMethodCall(const Expr* e) {
  if (e->kind != ExprKind::kCall) return false;
  const Expr* callee = e->lhs;
  return callee && callee->kind == ExprKind::kMemberAccess && callee->rhs &&
         callee->rhs->kind == ExprKind::kIdentifier &&
         (callee->rhs->text == "rand_mode" ||
          callee->rhs->text == "constraint_mode");
}

static bool ExprCallsModeMethod(const Expr* e);

static bool ScalarExprFieldsCallModeMethod(const Expr* e) {
  for (const Expr* child : {e->lhs, e->rhs, e->base, e->index, e->index_end,
                            e->condition, e->true_expr, e->false_expr,
                            e->repeat_count, e->with_expr, e->stream_range}) {
    if (ExprCallsModeMethod(child)) return true;
  }
  return false;
}

static bool ListExprFieldsCallModeMethod(const Expr* e) {
  for (const auto* a : e->args)
    if (ExprCallsModeMethod(a)) return true;
  for (const auto* el : e->elements)
    if (ExprCallsModeMethod(el)) return true;
  return false;
}

static bool AnyChildExprCallsModeMethod(const Expr* e) {
  return ScalarExprFieldsCallModeMethod(e) || ListExprFieldsCallModeMethod(e);
}

static bool ExprCallsModeMethod(const Expr* e) {
  if (!e) return false;
  if (IsModeMethodCall(e)) return true;
  return AnyChildExprCallsModeMethod(e);
}

static bool StmtCallsModeMethod(const Stmt* s);

static bool StmtExprFieldsCallModeMethod(const Stmt* s) {
  bool found = false;
  ForEachChildExpr(s, [&](Expr* const& e) {
    if (found) return;
    found = ExprCallsModeMethod(e);
  });
  return found;
}

static bool StmtChildrenCallModeMethod(const Stmt* s) {
  bool found = false;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (found) return;
    found = StmtCallsModeMethod(sub);
  });
  return found;
}

static bool StmtCallsModeMethod(const Stmt* s) {
  if (!s) return false;
  if (StmtExprFieldsCallModeMethod(s)) return true;
  return StmtChildrenCallModeMethod(s);
}

static void ValidateConstraintCallee(const ConstraintFunctionCallRef& ref,
                                     const ModuleItem* fn, DiagEngine& diag) {
  for (const auto& arg : fn->func_args) {
    bool bad = arg.direction == Direction::kOutput ||
               arg.direction == Direction::kInout ||
               (arg.direction == Direction::kRef && !arg.is_const);
    if (bad) {
      diag.Error(ref.loc,
                 std::format("function '{}' is called in a constraint, so each "
                             "of its arguments must be an input or a const ref",
                             ref.callee),
                 Subclause("18.5.11"));
      break;
    }
  }
  for (const auto* s : fn->func_body_stmts) {
    if (StmtCallsModeMethod(s)) {
      diag.Error(
          ref.loc,
          std::format("function '{}' used in a constraint cannot modify the "
                      "constraints by calling rand_mode or constraint_mode",
                      ref.callee),
          Subclause("18.5.11"));
      break;
    }
  }
}

void ClassConstraintValidator::ValidateOneClassConstraintFunctionArgs(
    const ClassDecl* cls) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    for (const auto& ref : m->constraint_function_call_refs) {
      const ModuleItem* fn = FindClassFunction(cls, ref.callee, unit_);
      if (!fn) continue;
      ValidateConstraintCallee(ref, fn, diag_);
    }
  }
}

void ClassConstraintValidator::ValidateConstraintFunctionArgs() {
  for (const auto* cls : AllClassDecls(unit_))
    ValidateOneClassConstraintFunctionArgs(cls);
}

static void ValidatePrePostRandomizePrototype(const ClassMember* m,
                                              DiagEngine& diag) {
  const ModuleItem* fn = m->method;
  if (!fn) return;
  std::string_view name = fn->name;
  if (fn->kind != ModuleItemKind::kFunctionDecl) {
    diag.Error(m->loc,
               std::format("'{}' shall be a void function taking no "
                           "arguments, not a task",
                           name),
               Subclause("18.6.2"));
    return;
  }
  if (fn->return_type.kind != DataTypeKind::kVoid) {
    diag.Error(m->loc, std::format("'{}' shall have a void return type", name),
               Subclause("18.6.2"));
  }
  if (!fn->func_args.empty()) {
    diag.Error(m->loc, std::format("'{}' shall take no arguments", name),
               Subclause("18.6.2"));
  }
}

void ClassConstraintValidator::ValidateOneClassBuiltinMethods(
    const ClassDecl* cls) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kMethod) continue;
    std::string_view name = m->method ? m->method->name : m->name;
    if (name == "rand_mode") {
      diag_.Error(m->loc,
                  "'rand_mode' is a built-in method and cannot be overridden",
                  Subclause("18.8"));
    }
    if (name == "constraint_mode") {
      diag_.Error(
          m->loc,
          "'constraint_mode' is a built-in method and cannot be overridden",
          Subclause("18.9"));
    }
    if (name == "randomize") {
      diag_.Error(m->loc,
                  "'randomize' is a built-in method and cannot be overridden",
                  Subclause("18.6.3"));
    }
    if (name == "pre_randomize" || name == "post_randomize") {
      ValidatePrePostRandomizePrototype(m, diag_);
    }
  }
}

void ClassConstraintValidator::ValidateBuiltinRandomizationMethods() {
  for (const auto* cls : AllClassDecls(unit_))
    ValidateOneClassBuiltinMethods(cls);
}

static bool LocStrictlyBefore(const SourceLoc& a, const SourceLoc& b) {
  if (a.file_id != b.file_id) return false;
  if (a.line != b.line) return a.line < b.line;
  return a.column < b.column;
}

static ClassDecl* ExternalBlockClass(const CompilationUnit* unit,
                                     const ExternalConstraintBlock& ext) {
  if (ext.scope_items == nullptr) {
    for (auto* cls : unit->classes) {
      if (cls->name == ext.class_name) return cls;
    }
    return nullptr;
  }
  for (const auto* item : *ext.scope_items) {
    if (item->kind == ModuleItemKind::kClassDecl &&
        item->class_decl != nullptr &&
        item->class_decl->name == ext.class_name) {
      return item->class_decl;
    }
  }
  return nullptr;
}

static void ValidateOnePrototypeCompletion(const ClassMember* m,
                                           const ClassDecl* cls,
                                           const CompilationUnit* unit,
                                           DiagEngine& diag) {
  std::string_view cls_name = cls->name;
  int matches = 0;
  for (const auto& ext : unit->external_constraints) {
    if (ext.constraint_name == m->name &&
        ExternalBlockClass(unit, ext) == cls) {
      ++matches;
    }
  }

  if (matches == 0) {
    if (m->is_constraint_extern) {
      diag.Error(m->loc,
                 std::format("explicit constraint prototype '{}' in class "
                             "'{}' has no external constraint block",
                             m->name, cls_name),
                 Subclause("18.5.1"));
    }
  } else if (matches > 1) {
    diag.Error(m->loc,
               std::format("constraint prototype '{}' in class '{}' is "
                           "completed by more than one external constraint "
                           "block",
                           m->name, cls_name),
               Subclause("18.5.1"));
  }
}

void ClassConstraintValidator::ValidateOneClassExternalConstraints(
    const ClassDecl* cls) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    if (!m->is_constraint_prototype) continue;
    if (m->is_pure_virtual) continue;
    ValidateOnePrototypeCompletion(m, cls, unit_, diag_);
  }
}

static const ClassMember* FindBaseConstraint(const ClassDecl* cls,
                                             std::string_view name,
                                             const CompilationUnit* unit) {
  if (cls->base_class.empty()) return nullptr;
  for (const auto* c = FindBaseClass(cls, unit); c;
       c = FindBaseClass(c, unit)) {
    for (const auto* m : c->members) {
      if (m->kind == ClassMemberKind::kConstraint && m->name == name) {
        return m;
      }
    }
  }
  return nullptr;
}

static const ClassMember* FindBaseFinalConstraint(const ClassDecl* cls,
                                                  std::string_view name,
                                                  const CompilationUnit* unit) {
  if (cls->base_class.empty()) return nullptr;
  for (const auto* c = FindBaseClass(cls, unit); c;
       c = FindBaseClass(c, unit)) {
    for (const auto* m : c->members) {
      if (m->kind == ClassMemberKind::kConstraint && m->name == name &&
          m->is_constraint_final) {
        return m;
      }
    }
  }
  return nullptr;
}

void ClassConstraintValidator::ValidateOneConstraintOverride(
    const ClassDecl* cls, const ClassMember* m) {
  if (m->is_constraint_initial && m->is_constraint_extends) {
    diag_.Error(m->loc,
                std::format("constraint '{}' shall not specify both ':initial' "
                            "and ':extends'",
                            m->name),
                Subclause("18.5.2"));
  }

  if (m->is_static && (m->is_constraint_initial || m->is_constraint_extends ||
                       m->is_constraint_final)) {
    diag_.Error(m->loc,
                std::format("static constraint '{}' shall not carry a dynamic "
                            "override specifier",
                            m->name),
                Subclause("18.5.10"));
  }

  const auto* base = FindBaseConstraint(cls, m->name, unit_);

  if (base != nullptr && base->is_pure_virtual && !m->is_pure_virtual &&
      m->is_static != base->is_static) {
    diag_.Error(
        m->loc,
        std::format("constraint '{}' overriding a pure constraint shall "
                    "match its 'static' qualification",
                    m->name),
        Subclause("18.5.10"));
  }

  if (m->is_constraint_initial && base) {
    diag_.Error(m->loc,
                std::format("constraint '{}' declared ':initial' overrides a "
                            "constraint of the same name in a base class",
                            m->name),
                Subclause("18.5.2"));
  }
  if (m->is_constraint_extends && !base) {
    diag_.Error(m->loc,
                std::format("constraint '{}' declared ':extends' does not "
                            "override a constraint in a base class",
                            m->name),
                Subclause("18.5.2"));
  }

  if (base != nullptr && FindBaseFinalConstraint(cls, m->name, unit_)) {
    diag_.Error(m->loc,
                std::format("constraint '{}' replaces a base class constraint "
                            "declared ':final'",
                            m->name),
                Subclause("18.5.2"));
  }
}

static void CollectInheritedPureConstraints(
    const ClassDecl* cls, const CompilationUnit* unit,
    std::vector<std::string_view>& pure_names) {
  if (!cls) return;
  if (!cls->base_class.empty()) {
    CollectInheritedPureConstraints(FindBaseClass(cls, unit), unit, pure_names);
  }
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint) continue;
    if (m->is_pure_virtual) {
      pure_names.push_back(m->name);
    } else {
      std::erase(pure_names, m->name);
    }
  }
}

void ClassConstraintValidator::ValidateNonAbstractPureConstraints(
    const ClassDecl* cls) {
  if (cls->is_virtual) return;

  std::vector<std::string_view> unimpl;
  if (!cls->base_class.empty()) {
    CollectInheritedPureConstraints(FindBaseClass(cls, unit_), unit_, unimpl);
  }
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kConstraint && !m->is_pure_virtual) {
      std::erase(unimpl, m->name);
    }
  }
  for (auto name : unimpl) {
    diag_.Error(cls->range.start,
                std::format("non-abstract class '{}' does not implement "
                            "inherited pure constraint '{}'",
                            cls->name, name),
                Subclause("18.5.2"));
  }
}

void ClassConstraintValidator::ValidateConstraintSpecifierParity(
    const ClassDecl* cls, const ClassMember* m) {
  for (const auto& ext : unit_->external_constraints) {
    if (ext.constraint_name != m->name || ExternalBlockClass(unit_, ext) != cls)
      continue;
    if (m->is_constraint_initial != ext.is_initial ||
        m->is_constraint_extends != ext.is_extends ||
        m->is_constraint_final != ext.is_final) {
      diag_.Error(
          ext.loc,
          std::format("external constraint block '{}::{}' and its prototype "
                      "disagree on dynamic override specifiers",
                      cls->name, m->name),
          Subclause("18.5.2"));
    }
    if (m->is_static != ext.is_static) {
      diag_.Error(
          ext.loc,
          std::format("external constraint block '{}::{}' and its prototype "
                      "disagree on the 'static' qualifier",
                      cls->name, m->name),
          Subclause("18.5.10"));
    }
  }
}

static void ValidatePureConstraintConflicts(const ClassDecl* cls,
                                            const ClassMember* m,
                                            const CompilationUnit* unit,
                                            DiagEngine& diag) {
  for (const auto& ext : unit->external_constraints) {
    if (ext.constraint_name == m->name &&
        ExternalBlockClass(unit, ext) == cls) {
      diag.Error(
          ext.loc,
          std::format("external constraint block '{}::{}' conflicts with "
                      "a pure constraint of the same name",
                      cls->name, m->name),
          Subclause("18.5.2"));
      break;
    }
  }
  for (const auto* other : cls->members) {
    if (other == m) continue;
    if (other->kind != ClassMemberKind::kConstraint) continue;
    if (other->name != m->name) continue;
    if (other->is_pure_virtual) continue;
    diag.Error(other->loc,
               std::format("constraint '{}' in class '{}' conflicts "
                           "with a pure constraint of the same name",
                           other->name, cls->name),
               Subclause("18.5.2"));
  }
}

void ClassConstraintValidator::ValidateConstraintInheritance() {
  for (const auto* cls : AllClassDecls(unit_)) {
    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kConstraint) continue;
      if (m->is_pure_virtual && !cls->is_virtual) {
        diag_.Error(m->loc,
                    std::format("pure constraint '{}' needs an abstract class, "
                                "and class '{}' is not declared virtual",
                                m->name, cls->name),
                    Subclause("18.5.2"));
      }
      if (m->is_pure_virtual) {
        ValidatePureConstraintConflicts(cls, m, unit_, diag_);
      } else if (m->is_constraint_prototype) {
        ValidateConstraintSpecifierParity(cls, m);
      }
      ValidateOneConstraintOverride(cls, m);
    }
    ValidateNonAbstractPureConstraints(cls);
  }
}

void ClassConstraintValidator::ValidateExternalConstraints() {
  for (const auto* cls : AllClassDecls(unit_)) {
    ValidateOneClassExternalConstraints(cls);
  }

  for (const auto& ext : unit_->external_constraints) {
    const ClassDecl* target = ExternalBlockClass(unit_, ext);
    if (target == nullptr) {
      diag_.Error(
          ext.loc,
          std::format("external constraint block '{}::{}' has no class '{}' "
                      "declared in its own scope",
                      ext.class_name, ext.constraint_name, ext.class_name),
          Subclause("18.5.1"));
      continue;
    }
    if (LocStrictlyBefore(ext.loc, target->range.end)) {
      diag_.Error(
          ext.loc,
          std::format("external constraint block '{}::{}' comes before the "
                      "declaration of class '{}' ends",
                      ext.class_name, ext.constraint_name, ext.class_name),
          Subclause("18.5.1"));
    }
  }
}

template <typename T>
static void AppendAll(std::vector<T>& dst, const std::vector<T>& src) {
  dst.insert(dst.end(), src.begin(), src.end());
}

static void CompleteOneExternalConstraint(ClassDecl* cls,
                                          const ExternalConstraintBlock& ext) {
  const ClassMember* body = ext.body;
  for (auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kConstraint ||
        !m->is_constraint_prototype || m->name != ext.constraint_name) {
      continue;
    }
    AppendAll(m->constraint_foreach_refs, body->constraint_foreach_refs);
    AppendAll(m->constraint_solve_before_refs,
              body->constraint_solve_before_refs);
    AppendAll(m->constraint_function_call_refs,
              body->constraint_function_call_refs);
    AppendAll(m->constraint_soft_refs, body->constraint_soft_refs);
    AppendAll(m->constraint_exprs, body->constraint_exprs);
    AppendAll(m->constraint_dist_refs, body->constraint_dist_refs);
    AppendAll(m->constraint_disable_soft_refs,
              body->constraint_disable_soft_refs);
    AppendAll(m->constraint_soft_exprs, body->constraint_soft_exprs);
    AppendAll(m->constraint_soft_dist_refs, body->constraint_soft_dist_refs);
    AppendAll(m->constraint_unique_refs, body->constraint_unique_refs);
    AppendAll(m->constraint_items, body->constraint_items);
    m->constraint_items_parsed = body->constraint_items_parsed;
  }
}

void ClassConstraintValidator::CompleteExternalConstraints() {
  for (const auto& ext : unit_->external_constraints) {
    ClassDecl* cls = ExternalBlockClass(unit_, ext);
    if (cls != nullptr) CompleteOneExternalConstraint(cls, ext);
  }
}

}  // namespace delta
