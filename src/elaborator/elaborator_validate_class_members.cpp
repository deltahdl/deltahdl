// The class rules other than §8.10 and §8.11: extending a class declared
// `:final` (§8.13), what `super` may name (§8.15), chaining constructors and
// the `default` keyword in a constructor argument list (§8.17), an embedded
// covergroup's assignment and a derived covergroup's base (§19.4, §19.4.1),
// and a weak_reference property's type argument (§8.30.1). It also applies the
// automatic lifetime a class method takes by default, which reports nothing.
// §8.10 and §8.11 are in elaborator_validate_static_methods.cpp, which the
// 1000-line cap in .github/workflows/deltahdl.yml separated from this file.

#include <format>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

void Elaborator::ValidateFinalClassExtension() {
  auto check = [&](const ClassDecl* cls) {
    if (cls->base_class.empty()) return;

    if (cls->base_class == "process") {
      diag_.Error(cls->range.start, "cannot extend a class declared ':final'",
                  Subclause("8.13"));
      return;
    }
    const auto* base = FindClassDecl(cls->base_class, unit_);
    if (base && base->is_final) {
      diag_.Error(cls->range.start, "cannot extend a class declared ':final'",
                  Subclause("8.13"));
    }
  };
  for (const auto* cls : unit_->classes) {
    check(cls);
  }
}

// §8.30.1: a weak_reference incorporated into another object as a class
// property carries the same parameter restriction as a standalone variable or a
// subroutine argument — its type argument shall name a class type. Any other
// type argument is a compile error, mirroring the variable-declaration and
// subroutine-argument checks elsewhere in the elaborator.
void Elaborator::ValidateWeakReferenceMembers() {
  auto check_member = [&](const ClassMember* m) {
    if (m->kind != ClassMemberKind::kProperty) return;
    if (m->data_type.kind != DataTypeKind::kNamed) return;
    if (m->data_type.type_name != "weak_reference") return;
    if (m->data_type.type_params.empty()) return;
    const auto& tp = m->data_type.type_params[0];
    if (!WeakRefTypeParamNamesClass(tp, typedefs_, class_names_)) {
      diag_.Error(m->loc, "weak_reference type parameter shall be a class type",
                  Subclause("8.30.1"));
    }
  };
  for (const auto* cls : unit_->classes) {
    for (const auto* m : cls->members) {
      check_member(m);
    }
  }
}

static bool IsSuperNewCall(const Stmt* s) {
  if (!s || s->kind != StmtKind::kExprStmt || !s->expr) return false;
  const auto* call = s->expr;
  if (call->kind != ExprKind::kCall) return false;
  const auto* callee = call->lhs;
  if (!callee || callee->kind != ExprKind::kMemberAccess) return false;
  bool lhs_is_super = callee->lhs &&
                      callee->lhs->kind == ExprKind::kIdentifier &&
                      callee->lhs->text == "super";
  bool rhs_is_new = callee->rhs && callee->rhs->kind == ExprKind::kIdentifier &&
                    callee->rhs->text == "new";
  return lhs_is_super && rhs_is_new;
}

// §8.17: returns whether a statement subtree contains a super.new() call. The
// question is only where the call stands, so no statement position is exempt
// and the list of child links descended is the one ForEachChildStmt in
// elaborator_validate_internal.h states; this walk names no link itself. It
// wrote out six of the thirteen, so a call in a fork arm
// (`fork super.new(); join_none`) or in an immediate assertion's action block
// (`assert (c) super.new();`) was not found.
//
// ForEachChildStmt gives the visitor no way to stop, so the first hit is kept
// in `found` and the recursion runs only while `found` is false.
static bool StmtSubtreeHasSuperNew(const Stmt* s) {
  if (!s) return false;
  if (IsSuperNewCall(s)) return true;
  bool found = false;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (found) return;
    found = StmtSubtreeHasSuperNew(sub);
  });
  return found;
}

// §8.17 states "To use this approach, super.new(...) shall be the first
// executable statement in the function new." This returns whether a
// super.new() call stands somewhere that sentence rules out, meaning a
// position it can never be the first executable statement from however the
// source is written. A non-first sequential call is handled instead by the
// index check in ReportSequentialSuperNew.
//
// The list of child links descended is the one ForEachChildStmt in
// elaborator_validate_internal.h states, and this walk names no link itself.
// What §8.17 decides is which of two treatments a link gets:
//
// Stmt::stmts does not guard. §9.3.1 runs the statements of a begin-end block
// in the order written, so a super.new() written first inside a block that is
// itself the constructor's first statement is the first executable statement
// of function new. The recursion through that link therefore carries on
// asking this same question rather than answering yes.
//
// The other twelve links guard, because reaching a statement under one of them
// takes something else first: an if evaluating its condition, a loop
// iterating, a case arm being selected, a for step running after a body, a
// randcase arm winning the weighted draw (§18.16), a randsequence production
// being reached (§18.17), an immediate assertion having already passed or
// failed to reach its action block (§16.3), or a fork arm being scheduled,
// which §9.3.2 orders in no defined way against its siblings. A super.new()
// below any of them is not the first executable statement, so it is reported.
//
// Six links were written out before and none of the seven guarding ones among
// them, so `fork super.new(); join_none` and `assert (c) super.new();` in a
// constructor were answered "not guarded" and went unreported.
//
// ForEachChildStmt gives the visitor no way to stop, so the first hit is kept
// in `found` and the recursion runs only while `found` is false.
static bool ConstructorHasGuardedSuperNew(const Stmt* s) {
  if (!s) return false;
  if (s->kind == StmtKind::kBlock) {
    for (const auto* sub : s->stmts) {
      if (ConstructorHasGuardedSuperNew(sub)) return true;
    }
    return false;
  }
  bool found = false;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (found) return;
    found = StmtSubtreeHasSuperNew(sub);
  });
  return found;
}

// Returns the new() constructor member of a class, or nullptr if absent.
static const ClassMember* FindClassConstructor(const ClassDecl* cls) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method &&
        m->method->name == "new") {
      return m;
    }
  }
  return nullptr;
}

// §8.17: scans the top-level sequential statements of a constructor for a
// super.new() call. Emits an error if one is present but is not the first
// executable statement. Returns whether such a sequential call was found.
static bool ReportSequentialSuperNew(const ModuleItem* method,
                                     DiagEngine& diag) {
  const auto& stmts = method->func_body_stmts;
  for (size_t i = 0; i < stmts.size(); ++i) {
    if (!IsSuperNewCall(stmts[i])) continue;
    if (i != 0) {
      diag.Error(stmts[i]->range.start,
                 "super.new() shall be the first executable statement "
                 "in the constructor",
                 Subclause("8.17"));
    }
    return true;
  }
  return false;
}

// §8.17: emits an error if a super.new() call appears in a control-flow
// position of the constructor (where it can never be the first statement).
static void ReportGuardedSuperNew(const ModuleItem* method, DiagEngine& diag) {
  for (const auto* s : method->func_body_stmts) {
    if (ConstructorHasGuardedSuperNew(s)) {
      diag.Error(s->range.start,
                 "super.new() shall be the first executable statement "
                 "in the constructor",
                 Subclause("8.17"));
      return;
    }
  }
}

void Elaborator::ValidateOneClassChainingCtor(const ClassDecl* cls) {
  if (cls->base_class.empty()) return;
  const ClassMember* ctor = FindClassConstructor(cls);
  if (!ctor || !ctor->method) return;
  bool has_super_new = ReportSequentialSuperNew(ctor->method, diag_);
  if (!has_super_new) ReportGuardedSuperNew(ctor->method, diag_);
  if (has_super_new &&
      (!cls->extends_args.empty() || cls->extends_has_default)) {
    diag_.Error(ctor->method->loc,
                "constructor shall not contain super.new() when extends "
                "specifier has arguments",
                Subclause("8.17"));
  }
}

// §19.4: identifies the embedded covergroup targeted by an assignment's
// left-hand side, or an empty view when the target is not a covergroup. The
// covergroup instance variable can be named either bare (`cg = new`) or through
// an explicit object handle inside the class (`this.cg = new`); both forms name
// the same variable and both are subject to the assignment restriction.
static std::string_view AssignedCovergroupName(
    const Expr* lhs, const std::unordered_set<std::string_view>& cg_names) {
  if (lhs == nullptr) return {};
  if (lhs->kind == ExprKind::kIdentifier && cg_names.count(lhs->text)) {
    return lhs->text;
  }
  // `this.cg` is a member access with the `.` operator (not `::`) whose base is
  // `this` and whose member names an embedded covergroup of this class.
  if (lhs->kind == ExprKind::kMemberAccess && !lhs->is_scope_resolution &&
      lhs->lhs != nullptr && lhs->lhs->kind == ExprKind::kIdentifier &&
      lhs->lhs->text == "this" && lhs->rhs != nullptr &&
      lhs->rhs->kind == ExprKind::kIdentifier &&
      cg_names.count(lhs->rhs->text)) {
    return lhs->rhs->text;
  }
  return {};
}

// §19.4: a covergroup declared inside a class is an embedded covergroup whose
// identifier names an implicitly declared instance variable. That variable is
// instantiated by assigning the result of new() to it inside the enclosing
// class's new() method, and the standard requires it not be assigned anywhere
// outside that constructor. Any assignment to the covergroup identifier from
// another method of the same class therefore violates the rule.
static void CheckCovergroupAssignStmt(
    const Stmt* s, const std::unordered_set<std::string_view>& cg_names,
    DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kBlockingAssign ||
      s->kind == StmtKind::kNonblockingAssign) {
    std::string_view cg = AssignedCovergroupName(s->lhs, cg_names);
    if (!cg.empty()) {
      diag.Error(s->range.start,
                 std::format("embedded covergroup '{}' shall only be assigned "
                             "inside the new() method of its class",
                             cg),
                 Subclause("19.4"));
    }
  }
  // §19.4 forbids the assignment outside new() and names no statement it is
  // permitted in, so this descends every link ForEachChildStmt in
  // elaborator_validate_internal.h states and names none itself. It wrote out
  // six of the thirteen, so `fork cg = new; join_none` and
  // `assert (en) cg = new;` in a method other than new() were never read.
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CheckCovergroupAssignStmt(sub, cg_names, diag);
  });
}

// §19.4: collects the names of all embedded covergroups declared in the class.
static std::unordered_set<std::string_view> CollectCovergroupNames(
    const ClassDecl* cls) {
  std::unordered_set<std::string_view> cg_names;
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kCovergroup && !m->name.empty()) {
      cg_names.insert(m->name);
    }
  }
  return cg_names;
}

// §19.4: checks every non-constructor method of the class for assignments to an
// embedded covergroup identifier, which are forbidden outside new().
static void CheckClassMethodsForCovergroupAssign(
    const ClassDecl* cls, const std::unordered_set<std::string_view>& cg_names,
    DiagEngine& diag) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
    // The constructor is the one place an embedded covergroup may be
    // instantiated, so assignments there are permitted.
    if (m->method->name == "new") continue;
    for (const auto* s : m->method->func_body_stmts) {
      CheckCovergroupAssignStmt(s, cg_names, diag);
    }
  }
}

void Elaborator::ValidateEmbeddedCovergroupAssign() {
  for (const auto* cls : unit_->classes) {
    std::unordered_set<std::string_view> cg_names = CollectCovergroupNames(cls);
    if (cg_names.empty()) continue;
    CheckClassMethodsForCovergroupAssign(cls, cg_names, diag_);
  }
}

// §19.4.1: a derived embedded covergroup, written `covergroup extends base ;`,
// inherits the covergroup named by `base`. It shall be an error to use the
// extends form when no covergroup of that name has previously been defined in a
// base class of the enclosing class. The search starts at the immediate base
// class and follows the inheritance chain upward; a covergroup defined in the
// derived class itself does not satisfy the requirement.
static bool BaseClassDefinesCovergroup(const ClassDecl* cls,
                                       std::string_view cg_name,
                                       const CompilationUnit* unit) {
  for (const ClassDecl* base = cls->base_class.empty()
                                   ? nullptr
                                   : FindClassDecl(cls->base_class, unit);
       base; base = base->base_class.empty()
                        ? nullptr
                        : FindClassDecl(base->base_class, unit)) {
    for (const auto* m : base->members) {
      if (m->kind == ClassMemberKind::kCovergroup && m->name == cg_name) {
        return true;
      }
    }
  }
  return false;
}

void Elaborator::ValidateDerivedCovergroupBase() {
  for (const auto* cls : unit_->classes) {
    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kCovergroup) continue;
      if (m->covergroup_extends_base.empty()) continue;
      if (!BaseClassDefinesCovergroup(cls, m->covergroup_extends_base, unit_)) {
        diag_.Error(
            m->loc,
            std::format("derived covergroup cannot extend '{}': no covergroup "
                        "of that name is defined in a base class",
                        m->covergroup_extends_base),
            Subclause("19.4.1"));
      }
    }
  }
}

void Elaborator::ValidateClassMethodBodies(const ModuleDecl* decl) {
  auto validate_class_methods = [&](const ClassDecl* cls) {
    for (const auto* m : cls->members) {
      if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
      ValidateFunctionBody(m->method);
    }
  };
  for (const auto* cls : unit_->classes) {
    validate_class_methods(cls);
  }
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kClassDecl || !item->class_decl) continue;
    validate_class_methods(item->class_decl);
  }
}

static void ApplyAutoToClassMethods(const ClassDecl* cls) {
  if (!cls) return;
  for (auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method &&
        !m->method->is_automatic && !m->method->is_static) {
      m->method->is_automatic = true;
    }

    if (m->kind == ClassMemberKind::kClassDecl && m->nested_class) {
      ApplyAutoToClassMethods(m->nested_class);
    }
  }
}

void Elaborator::ApplyClassMethodAutomaticDefault() {
  for (auto* cls : unit_->classes) ApplyAutoToClassMethods(cls);
  for (auto* mod : unit_->modules) {
    for (auto* item : mod->items) {
      if (item->kind == ModuleItemKind::kClassDecl) {
        ApplyAutoToClassMethods(item->class_decl);
      }
    }
  }
  for (auto* pkg : unit_->packages) {
    for (auto* item : pkg->items) {
      if (item->kind == ModuleItemKind::kClassDecl) {
        ApplyAutoToClassMethods(item->class_decl);
      }
    }
  }
}

static bool ExprRefsSuper(const Expr* e) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier && e->text == "super") return true;
  if (ExprRefsSuper(e->lhs) || ExprRefsSuper(e->rhs) ||
      ExprRefsSuper(e->base) || ExprRefsSuper(e->index) ||
      ExprRefsSuper(e->condition) || ExprRefsSuper(e->true_expr) ||
      ExprRefsSuper(e->false_expr) || ExprRefsSuper(e->with_expr)) {
    return true;
  }
  for (const auto* elem : e->elements)
    if (ExprRefsSuper(elem)) return true;
  for (const auto* arg : e->args)
    if (ExprRefsSuper(arg)) return true;
  return false;
}

// §8.15 conditions the rule on the class rather than on the statement the
// reference is written in, so this descends every link ForEachChildStmt in
// elaborator_validate_internal.h states and names none itself. It wrote out
// six of the thirteen, so `fork x = super.y; join_none` and
// `assert (1) x = super.y;` in a class that extends nothing were never read.
//
// ForEachChildStmt gives the visitor no way to stop, so the first hit is kept
// in `found` and the recursion runs only while `found` is false.
static bool StmtRefsSuper(const Stmt* s) {
  if (!s) return false;
  if (ExprRefsSuper(s->lhs)) return true;
  if (ExprRefsSuper(s->rhs)) return true;
  if (ExprRefsSuper(s->expr)) return true;
  if (ExprRefsSuper(s->condition)) return true;
  bool found = false;
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    if (found) return;
    found = StmtRefsSuper(sub);
  });
  return found;
}

// §8.15: in a class that does not extend another, no method body may reference
// 'super'. Reports the first offending method statement.
static void CheckNonDerivedClassMethodsForSuper(const ClassDecl* cls,
                                                DiagEngine& diag) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
    for (const auto* s : m->method->func_body_stmts) {
      if (StmtRefsSuper(s)) {
        diag.Error(m->method->loc,
                   "'super' shall only be used in a derived class",
                   Subclause("8.15"));
        break;
      }
    }
  }
}

// Names the kind of parameter `name` is in `cls` itself, in §8.15's own words,
// or an empty view when `cls` does not declare it as a value parameter or a
// local value parameter. §6.20.3 type parameters share the parameter port list
// with value parameters and are passed over, because the sentence this serves
// is about a value parameter. §6.20.4 makes every parameter declared in a class
// body a local parameter, which is what Parser::ForceLocalparam records, so a
// member carrying is_param is a local value parameter whichever keyword
// declared it.
static std::string_view ParamKindIn(const ClassDecl* cls,
                                    std::string_view name) {
  for (const auto& p : cls->params) {
    if (p.first != name || cls->type_param_names.count(p.first)) continue;
    return cls->localparam_port_names.count(p.first) ? "local value parameter"
                                                     : "value parameter";
  }
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kProperty && m->is_param &&
        m->name == name) {
      return "local value parameter";
    }
  }
  return {};
}

// The class `cls` extends, or nullptr when it extends nothing or names a class
// `unit` does not declare.
static const ClassDecl* BaseOf(const ClassDecl* cls,
                               const CompilationUnit* unit) {
  if (cls->base_class.empty()) return nullptr;
  return FindClassDecl(cls->base_class, unit);
}

// §8.15: names the kind of parameter `name` is in the base class chain of
// `cls`, or an empty view when no base class declares it as a value parameter
// or a local value parameter. §8.15 places the declaration "a level up or ...
// inherited by the class one level up", so the search follows the base classes
// upward and stops on a chain that closes on itself.
static std::string_view SuperParamKind(const ClassDecl* cls,
                                       std::string_view name,
                                       const CompilationUnit* unit) {
  std::unordered_set<const ClassDecl*> seen;
  for (const ClassDecl* base = BaseOf(cls, unit);
       base && seen.insert(base).second; base = BaseOf(base, unit)) {
    std::string_view kind = ParamKindIn(base, name);
    if (!kind.empty()) return kind;
  }
  return {};
}

// §8.15: "An expression using super to access the value parameter or local
// value parameter is not a constant expression." Reports every `super.name`
// anywhere inside an expression the standard requires to be constant, where
// `name` is a value parameter or a local value parameter of a base class. A
// `super.name` naming anything else — an ordinary data member, a method — is
// left alone: it is not constant either, but for a reason §8.15 does not state,
// and a report here would name a rule the source did not break.
static void CheckConstExprForSuperParam(const Expr* e, const ClassDecl* cls,
                                        const CompilationUnit* unit,
                                        DiagEngine& diag) {
  if (!e) return;
  const Expr* access = e;
  if (access->kind == ExprKind::kMemberAccess && !access->is_scope_resolution &&
      access->lhs && access->lhs->kind == ExprKind::kIdentifier &&
      access->lhs->text == "super" && access->rhs &&
      access->rhs->kind == ExprKind::kIdentifier) {
    std::string_view name = access->rhs->text;
    std::string_view kind = SuperParamKind(cls, name, unit);
    if (!kind.empty()) {
      diag.Error(access->range.start,
                 std::format("expression using 'super' to access base class {} "
                             "'{}' is not a constant expression",
                             kind, name),
                 Subclause("8.15"));
      return;
    }
  }
  CheckConstExprForSuperParam(e->lhs, cls, unit, diag);
  CheckConstExprForSuperParam(e->rhs, cls, unit, diag);
  CheckConstExprForSuperParam(e->base, cls, unit, diag);
  CheckConstExprForSuperParam(e->index, cls, unit, diag);
  CheckConstExprForSuperParam(e->index_end, cls, unit, diag);
  CheckConstExprForSuperParam(e->repeat_count, cls, unit, diag);
  CheckConstExprForSuperParam(e->condition, cls, unit, diag);
  CheckConstExprForSuperParam(e->true_expr, cls, unit, diag);
  CheckConstExprForSuperParam(e->false_expr, cls, unit, diag);
  CheckConstExprForSuperParam(e->with_expr, cls, unit, diag);
  for (const auto* elem : e->elements)
    CheckConstExprForSuperParam(elem, cls, unit, diag);
  for (const auto* arg : e->args)
    CheckConstExprForSuperParam(arg, cls, unit, diag);
}

// The expressions a declaration inside a subroutine body requires to be
// constant: the initializer of a static variable, and each fixed-size unpacked
// dimension. §7.4.2 writes a fixed-size unpacked dimension as a range of two
// constant expressions or as a single positive constant integer expression.
static void CheckStmtConstantContexts(const Stmt* s, const ClassDecl* cls,
                                      const CompilationUnit* unit,
                                      DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kVarDecl) {
    if (s->var_is_static) {
      CheckConstExprForSuperParam(s->var_init, cls, unit, diag);
    }
    for (const auto* dim : s->var_unpacked_dims) {
      CheckConstExprForSuperParam(dim, cls, unit, diag);
    }
  }
  // §8.15 bars the reach through 'super' wherever a constant expression is
  // required and puts no condition on the statement the declaration stands in,
  // so this reaches every position ForEachChildStmt in
  // elaborator_validate_internal.h names. Stmt::for_steps is descended and
  // holds no declaration to check, A.6.8 admitting in it an
  // operator_assignment, an inc_or_dec_expression or a call and nothing else.
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CheckStmtConstantContexts(sub, cls, unit, diag);
  });
}

// §8.15: checks every method body of a derived class for a base class value
// parameter or local value parameter reached through 'super' where a constant
// expression is required.
static void CheckSuperParamInConstantExpr(const ClassDecl* cls,
                                          const CompilationUnit* unit,
                                          DiagEngine& diag) {
  for (const auto* m : cls->members) {
    if (m->kind != ClassMemberKind::kMethod || !m->method) continue;
    for (const auto* s : m->method->func_body_stmts) {
      CheckStmtConstantContexts(s, cls, unit, diag);
    }
  }
}

// §8.15 states two rules about 'super', and this applies both. Its name says
// 'super' rather than either rule because whether a class extends another
// decides which of the two it can breach, so neither name would cover the
// classes this walks.
void Elaborator::ValidateSuperRules() {
  for (const auto* cls : unit_->classes) {
    // §8.15 states two rules about 'super' and whether the class extends
    // another decides which one it can breach: a class with no base class may
    // not name 'super' at all, and a class with one may not reach a base class
    // value parameter or local value parameter through it where a constant
    // expression is required.
    if (cls->base_class.empty()) {
      CheckNonDerivedClassMethodsForSuper(cls, diag_);
    } else {
      CheckSuperParamInConstantExpr(cls, unit_, diag_);
    }
  }
}

// §8.17: returns the class's own 'new' constructor method, or null if the
// class declares none.
static const ModuleItem* FindClassCtorMethod(const ClassDecl* cls) {
  if (!cls) return nullptr;
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method &&
        m->method->name == "new") {
      return m->method;
    }
  }
  return nullptr;
}

// §8.17: returns whether an expression tree references any identifier whose
// name appears in 'names'. Mirrors the traversal used for 'super' detection.
static bool ExprRefsAnyName(const Expr* e,
                            const std::unordered_set<std::string_view>& names) {
  if (!e) return false;
  if (e->kind == ExprKind::kIdentifier && names.count(e->text)) return true;
  if (ExprRefsAnyName(e->lhs, names) || ExprRefsAnyName(e->rhs, names) ||
      ExprRefsAnyName(e->base, names) || ExprRefsAnyName(e->index, names) ||
      ExprRefsAnyName(e->condition, names) ||
      ExprRefsAnyName(e->true_expr, names) ||
      ExprRefsAnyName(e->false_expr, names) ||
      ExprRefsAnyName(e->with_expr, names)) {
    return true;
  }
  for (const auto* elem : e->elements)
    if (ExprRefsAnyName(elem, names)) return true;
  for (const auto* arg : e->args)
    if (ExprRefsAnyName(arg, names)) return true;
  return false;
}

// §8.17: returns whether a constructor's argument list uses the 'default'
// keyword.
static bool CtorArgListUsesDefault(const ModuleItem* ctor) {
  if (!ctor) return false;
  for (const auto& arg : ctor->func_args) {
    if (arg.is_default) return true;
  }
  return false;
}

// §8.17: 'default' may be passed as the sole argument to super.new() only when
// the enclosing constructor's own argument list used the 'default' keyword.
// This handles the case where it did not, flagging any such super.new() call.
static void CheckDefaultArgInSuperNewCall(const ModuleItem* ctor,
                                          DiagEngine& diag) {
  for (const auto* s : ctor->func_body_stmts) {
    if (!IsSuperNewCall(s)) continue;
    const auto& call_args = s->expr->args;
    if (call_args.size() == 1 && call_args[0] &&
        call_args[0]->kind == ExprKind::kIdentifier &&
        call_args[0]->text == "default") {
      diag.Error(s->range.start,
                 "'default' may be passed to super.new() only when the "
                 "constructor argument list uses the 'default' keyword",
                 Subclause("8.17"));
    }
  }
}

// §8.17: because 'default' expands to the superclass constructor arguments, an
// explicit argument in the subclass constructor shall not share a name with any
// superclass constructor argument.
static void CheckDefaultCtorArgNameConflicts(const ModuleItem* ctor,
                                             const ModuleItem* base_ctor,
                                             DiagEngine& diag) {
  std::unordered_set<std::string_view> base_arg_names;
  for (const auto& a : base_ctor->func_args) {
    if (!a.name.empty()) base_arg_names.insert(a.name);
  }
  for (const auto& a : ctor->func_args) {
    if (a.is_default || a.name.empty()) continue;
    if (base_arg_names.count(a.name)) {
      diag.Error(ctor->loc,
                 std::format("constructor argument '{}' shall not share a "
                             "name with a superclass constructor argument "
                             "when 'default' is used",
                             a.name),
                 Subclause("8.17"));
    }
  }
}

// §8.17: 'default' shall not be used when a superclass constructor argument's
// default value refers to a local member of the superclass.
static void CheckDefaultCtorArgRefsBaseLocal(const ClassDecl* base,
                                             const ModuleItem* ctor,
                                             const ModuleItem* base_ctor,
                                             DiagEngine& diag) {
  std::unordered_set<std::string_view> base_locals;
  for (const auto* m : base->members) {
    if (m->is_local && !m->name.empty()) base_locals.insert(m->name);
  }
  if (base_locals.empty()) return;
  for (const auto& a : base_ctor->func_args) {
    if (a.default_value && ExprRefsAnyName(a.default_value, base_locals)) {
      diag.Error(ctor->loc,
                 "'default' shall not be used when a superclass constructor "
                 "argument default value refers to a local member",
                 Subclause("8.17"));
      break;
    }
  }
}

// §8.17: enforces the rules governing the 'default' keyword in a subclass
// constructor argument list and in an explicit super.new() call.
void Elaborator::ValidateOneClassDefaultKeyword(const ClassDecl* cls) {
  const ModuleItem* ctor = FindClassCtorMethod(cls);

  bool ctor_has_default = CtorArgListUsesDefault(ctor);

  // §8.17: 'default' expands to the superclass constructor's arguments, so the
  // class shall extend another class for the expansion to have a source.
  if (ctor_has_default && cls->base_class.empty()) {
    diag_.Error(ctor->loc,
                "'default' in a constructor argument list requires the class "
                "to extend a superclass",
                Subclause("8.17"));
  }

  // §8.17: when the extends specifier uses 'default' and the subclass also
  // defines its own constructor, that constructor's argument list shall repeat
  // the 'default' keyword.
  if (cls->extends_has_default && ctor && !ctor_has_default) {
    diag_.Error(ctor->loc,
                "constructor argument list shall contain 'default' when the "
                "extends specifier uses the 'default' keyword",
                Subclause("8.17"));
  }

  // §8.17: 'default' may be passed as the sole argument to super.new() only
  // when the constructor's own argument list used the 'default' keyword.
  if (ctor && !ctor_has_default) {
    CheckDefaultArgInSuperNewCall(ctor, diag_);
  }

  if (!ctor_has_default || cls->base_class.empty()) return;

  const ClassDecl* base = FindClassDecl(cls->base_class, unit_);
  const ModuleItem* base_ctor = FindClassCtorMethod(base);
  if (!base_ctor) return;

  CheckDefaultCtorArgNameConflicts(ctor, base_ctor, diag_);
  CheckDefaultCtorArgRefsBaseLocal(base, ctor, base_ctor, diag_);
}

void Elaborator::ValidateChainingConstructors() {
  for (const auto* cls : unit_->classes) {
    ValidateOneClassChainingCtor(cls);
    ValidateOneClassDefaultKeyword(cls);
  }
}

}  // namespace delta
