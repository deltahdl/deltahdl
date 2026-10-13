#include <format>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_classes.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/std_package.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

static bool IsCompoundAssignOp(TokenKind op) {
  switch (op) {
    case TokenKind::kPlusEq:
    case TokenKind::kMinusEq:
    case TokenKind::kStarEq:
    case TokenKind::kSlashEq:
    case TokenKind::kPercentEq:
    case TokenKind::kAmpEq:
    case TokenKind::kPipeEq:
    case TokenKind::kCaretEq:
    case TokenKind::kLtLtEq:
    case TokenKind::kGtGtEq:
    case TokenKind::kLtLtLtEq:
    case TokenKind::kGtGtGtEq:
      return true;
    default:
      return false;
  }
}

static bool IsClassVar(const Expr* e,
                       const std::unordered_set<std::string_view>& class_vars) {
  auto name = ExprIdent(e);
  if (name.empty()) return false;
  return class_vars.count(name) != 0;
}

static bool IsAllowedClassBinaryOp(TokenKind op) {
  return op == TokenKind::kEqEq || op == TokenKind::kBangEq ||
         op == TokenKind::kEqEqEq || op == TokenKind::kBangEqEq ||
         op == TokenKind::kEqEqQuestion || op == TokenKind::kBangEqQuestion;
}

// Returns true when any of *cls*'s directly listed interface types (the
// implements and extends-interface lists) is itself derived from *b*.
static bool AnyInterfaceDerivedFrom(const ClassDecl* cls, std::string_view b,
                                    const CompilationUnit* unit) {
  for (const auto& iface : cls->implements_types) {
    if (IsClassDerivedFrom(iface.name, b, unit)) return true;
  }
  for (const auto& iface : cls->extends_interfaces) {
    if (IsClassDerivedFrom(iface.name, b, unit)) return true;
  }
  return false;
}

bool IsClassDeclDerivedFrom(const ClassDecl* a, std::string_view b,
                            const CompilationUnit* unit) {
  for (const auto* cls = a; cls; cls = FindBaseClass(cls, unit)) {
    if (cls->base_class == b) return true;
    if (AnyInterfaceDerivedFrom(cls, b, unit)) return true;
  }
  return false;
}

bool IsClassDerivedFrom(std::string_view a, std::string_view b,
                        const CompilationUnit* unit) {
  if (a == b) return true;
  return IsClassDeclDerivedFrom(FindClassDecl(a, unit), b, unit);
}

static bool AreClassTypesComparable(std::string_view type_a,
                                    std::string_view type_b,
                                    const CompilationUnit* unit) {
  return IsClassDerivedFrom(type_a, type_b, unit) ||
         IsClassDerivedFrom(type_b, type_a, unit);
}

// §8.8: a typed constructor call writes the class scope before 'new' to fix
// the constructed object's type independently of the assignment target (e.g.
// Derived::new or Param#(...)::new). Return that scope type name when *rhs*
// is such a call, otherwise an empty view. The argument-less form is parsed
// as a bare scope-resolved member access; the parenthesized form is a call
// whose callee is that member access.
static std::string_view TypedConstructorScopeType(const Expr* rhs) {
  if (!rhs) return {};
  const Expr* access = nullptr;
  if (rhs->kind == ExprKind::kMemberAccess) {
    access = rhs;
  } else if (rhs->kind == ExprKind::kCall && rhs->lhs &&
             rhs->lhs->kind == ExprKind::kMemberAccess) {
    access = rhs->lhs;
  }
  if (!access) return {};
  if (!access->lhs || access->lhs->kind != ExprKind::kIdentifier) return {};
  if (!access->rhs || access->rhs->kind != ExprKind::kIdentifier) return {};
  if (access->rhs->text != "new") return {};
  return access->lhs->text;
}

// The tables the class-handle checks of one module read: the names of its
// class handle variables, the class each is declared with, and every
// variable's declared kind.
struct ClassHandleTables {
  const std::unordered_set<std::string_view>& class_vars;
  const std::unordered_map<std::string_view, std::string_view>& class_var_types;
  const std::unordered_map<std::string_view, DataTypeKind>& var_types;
  const CompilationUnit* unit;
};

// Whether `e` is plainly a value of an integral or real type, none of which a
// class handle is assignment compatible with (§11.4.5): a number, a real, a
// string or an unbased unsized literal, a variable declared with such a type,
// or an operator over such operands.
static bool IsPlainValue(
    const Expr* e,
    const std::unordered_map<std::string_view, DataTypeKind>& types) {
  switch (e->kind) {
    case ExprKind::kIntegerLiteral:
    case ExprKind::kRealLiteral:
    case ExprKind::kStringLiteral:
    case ExprKind::kUnbasedUnsizedLiteral:
      return true;
    case ExprKind::kIdentifier: {
      auto it = types.find(e->text);
      return it != types.end() &&
             (IsIntegralType(it->second) || IsRealType(it->second));
    }
    case ExprKind::kUnary:
      return IsPlainValue(e->lhs, types);
    case ExprKind::kBinary:
      return IsPlainValue(e->lhs, types) && IsPlainValue(e->rhs, types);
    default:
      return false;
  }
}

// Validates the operands of a binary expression that involves at least one
// class-handle variable: rejects disallowed operators and, for comparisons of
// two handles, requires assignment-compatible types.
static void CheckClassHandleBinary(const Expr* e, const ClassHandleTables& t,
                                   DiagEngine& diag) {
  const auto& class_vars = t.class_vars;
  const auto& class_var_types = t.class_var_types;
  const CompilationUnit* unit = t.unit;
  bool lhs_class =
      e->lhs && IsHandleOperand(e->lhs, class_vars, class_var_types, unit);
  bool rhs_class =
      e->rhs && IsHandleOperand(e->rhs, class_vars, class_var_types, unit);
  if ((lhs_class || rhs_class) && !IsAllowedClassBinaryOp(e->op)) {
    diag.Error(e->range.start,
               "operator is not allowed on class object handles",
               Subclause("8.4"));
  }

  // §11.4.5 (printed page 279): an equality operator takes a class handle
  // only against an operand assignment compatible with it, another handle or
  // null; a value of an integral or real type is none.
  if (lhs_class != rhs_class && IsAllowedClassBinaryOp(e->op) &&
      IsPlainValue(lhs_class ? e->rhs : e->lhs, t.var_types)) {
    diag.Error(e->range.start,
               "a class handle is compared only with a class handle or null",
               Subclause("11.4.5"));
  }

  if (lhs_class && rhs_class && IsAllowedClassBinaryOp(e->op)) {
    auto lhs_name = ExprIdent(e->lhs);
    auto rhs_name = ExprIdent(e->rhs);
    auto lt = class_var_types.find(lhs_name);
    auto rt = class_var_types.find(rhs_name);
    if (lt != class_var_types.end() && rt != class_var_types.end() &&
        !AreClassTypesComparable(lt->second, rt->second, unit)) {
      // §11.4.5 states the compatibility rule for the comparison: logical or
      // case equality on a class handle or the literal null is legal only when
      // one operand is assignment compatible with the other. §8.4 names only ==
      // and !=, while this site accepts ==, !=, ===, !==, ==? and !=?.
      diag.Error(e->range.start,
                 "class handle comparison requires assignment compatible "
                 "types",
                 Subclause("11.4.5"));
    }
  }
}

// Validates a cast expression: a class handle may not be cast to a non-class
// type, and a non-class value (other than 'null') may not be cast to a class
// type.
static void CheckClassHandleCast(
    const Expr* e, const std::unordered_set<std::string_view>& class_vars,
    const CompilationUnit* unit, DiagEngine& diag) {
  if (e->lhs && IsClassVar(e->lhs, class_vars) && !e->text.empty() &&
      !FindClassDecl(e->text, unit)) {
    diag.Error(e->range.start,
               "cannot cast class object handle to a non-class type",
               Subclause("8.4"));
  }

  if (!e->text.empty() && FindClassDecl(e->text, unit) != nullptr && e->lhs &&
      !IsClassVar(e->lhs, class_vars) &&
      (e->lhs->kind != ExprKind::kIdentifier || e->lhs->text != "null")) {
    diag.Error(e->range.start, "cannot cast non-class value to a class type",
               Subclause("8.4"));
  }
}

// §11.4.11 (printed page 286), case e): whether one class the class `a` is or
// derives from is one the class `b` is or derives from. Where `b` derives from
// `a` itself, or `a` names no class the unit declares -- a built-in class such
// as mailbox -- the first step answers.
static bool ShareABaseClass(std::string_view a, std::string_view b,
                            const CompilationUnit* unit) {
  if (IsClassDerivedFrom(b, a, unit)) return true;
  for (const auto* cls = FindClassDecl(a, unit); cls != nullptr;
       cls = FindBaseClass(cls, unit)) {
    if (IsClassDerivedFrom(b, cls->name, unit)) return true;
  }
  return false;
}

// §11.4.11: a conditional whose two operands are class handles is legal where
// one is assignment compatible with the other or both derive from a common
// base class. Two variables of unrelated class types are neither; a null
// operand is no variable and is legal with any handle.
static void CheckConditionalClassOperands(
    const Expr* e,
    const std::unordered_map<std::string_view, std::string_view>& types,
    const CompilationUnit* unit, DiagEngine& diag) {
  auto first = types.find(e->true_expr->text);
  auto second = types.find(e->false_expr->text);
  if (e->true_expr->kind != ExprKind::kIdentifier ||
      e->false_expr->kind != ExprKind::kIdentifier || first == types.end() ||
      second == types.end() ||
      ShareABaseClass(first->second, second->second, unit))
    return;
  diag.Error(e->range.start,
             std::format("conditional operands of class types '{}' and '{}' "
                         "share no base class and neither is assignment "
                         "compatible with the other",
                         first->second, second->second),
             Subclause("11.4.11"));
}

static void CheckClassHandleExpr(const Expr* e, const ClassHandleTables& t,
                                 DiagEngine& diag) {
  if (!e) return;
  const auto& class_vars = t.class_vars;
  const auto& class_var_types = t.class_var_types;
  const CompilationUnit* unit = t.unit;

  if (e->kind == ExprKind::kBinary) CheckClassHandleBinary(e, t, diag);
  if (e->kind == ExprKind::kTernary)
    CheckConditionalClassOperands(e, class_var_types, unit, diag);

  if (e->kind == ExprKind::kUnary &&
      IsHandleOperand(e->lhs, class_vars, class_var_types, unit)) {
    diag.Error(e->range.start,
               "operator is not allowed on class object handles",
               Subclause("8.4"));
  }

  if (e->kind == ExprKind::kPostfixUnary &&
      IsHandleOperand(e->lhs, class_vars, class_var_types, unit)) {
    diag.Error(e->range.start,
               "operator is not allowed on class object handles",
               Subclause("8.4"));
  }

  if (e->kind == ExprKind::kSelect && e->base &&
      IsClassVar(e->base, class_vars)) {
    diag.Error(e->range.start, "bit-select on class object handle is illegal",
               Subclause("8.4"));
  }

  if (e->kind == ExprKind::kCast) {
    CheckClassHandleCast(e, class_vars, unit, diag);
  }

  for (const Expr* child : {e->lhs, e->rhs, e->base, e->index, e->condition,
                            e->true_expr, e->false_expr})
    CheckClassHandleExpr(child, t, diag);
  for (const auto* elem : e->elements) CheckClassHandleExpr(elem, t, diag);
}

// Extracts the call expression a statement evaluates (directly as an expression
// statement or as the right-hand side of a blocking/nonblocking assignment),
// unwrapping a single enclosing cast. Returns nullptr when the statement does
// not evaluate a call.
static const Expr* ExtractCallFromStmt(const Stmt* s) {
  if (!s) return nullptr;
  const Expr* call = nullptr;
  if (s->kind == StmtKind::kExprStmt && s->expr) {
    call = s->expr;
  } else if ((s->kind == StmtKind::kBlockingAssign ||
              s->kind == StmtKind::kNonblockingAssign) &&
             s->rhs) {
    call = s->rhs;
  }
  if (call && call->kind == ExprKind::kCast && call->lhs) call = call->lhs;
  if (!call || call->kind != ExprKind::kCall) return nullptr;
  return call;
}

static void CheckInterfaceHandleRandConstraintMode(
    const Stmt* s,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  const Expr* call = ExtractCallFromStmt(s);
  if (!call) return;
  const Expr* callee = call->lhs;
  if (!callee || callee->kind != ExprKind::kMemberAccess) return;
  if (!callee->lhs || callee->lhs->kind != ExprKind::kIdentifier) return;
  if (!callee->rhs || callee->rhs->kind != ExprKind::kIdentifier) return;
  auto method_name = callee->rhs->text;
  if (method_name != "rand_mode" && method_name != "constraint_mode") return;
  auto var_name = callee->lhs->text;
  auto it = var_types.find(var_name);
  if (it == var_types.end()) return;
  const auto* cls = FindClassDecl(it->second, unit);
  if (!cls || !cls->is_interface) return;
  diag.Error(callee->range.start,
             std::format("'{}' is not legal on interface class handle '{}'",
                         method_name, var_name),
             Subclause("8.26.9"));
}

// Returns true when *cls* or any of its base classes declares a constraint
// block named *constraint_name*.
static bool ClassHierarchyHasConstraint(const ClassDecl* cls,
                                        std::string_view constraint_name,
                                        const CompilationUnit* unit) {
  for (const auto* c = cls; c; c = FindBaseClass(c, unit)) {
    for (const auto* m : c->members) {
      if (m->kind == ClassMemberKind::kConstraint &&
          m->name == constraint_name) {
        return true;
      }
    }
  }
  return false;
}

// Matches the named form obj.constraint_id.constraint_mode(...) of a call
// statement. On success returns the prefix member access (whose left side is
// the object handle identifier and whose right side is the constraint name),
// and nullptr otherwise.
static const Expr* MatchNamedConstraintModePrefix(const Stmt* s) {
  const Expr* call = ExtractCallFromStmt(s);
  if (!call) return nullptr;

  // callee must be <object>.<constraint_id>.constraint_mode
  const Expr* callee = call->lhs;
  if (!callee || callee->kind != ExprKind::kMemberAccess) return nullptr;
  if (!callee->rhs || callee->rhs->kind != ExprKind::kIdentifier)
    return nullptr;
  if (callee->rhs->text != "constraint_mode") return nullptr;

  // The named form prefixes the method with object.constraint_id, so the
  // receiver of constraint_mode is itself a member access whose left side is a
  // plain object handle and whose right side is the constraint name.
  const Expr* prefix = callee->lhs;
  if (!prefix || prefix->kind != ExprKind::kMemberAccess) return nullptr;
  if (!prefix->lhs || prefix->lhs->kind != ExprKind::kIdentifier)
    return nullptr;
  if (!prefix->rhs || prefix->rhs->kind != ExprKind::kIdentifier)
    return nullptr;
  return prefix;
}

// 18.9: a constraint_mode() call names a constraint block declared in the
// object's class hierarchy, and naming any other is a compile-time error. This
// applies only to the named form obj.constraint_id.constraint_mode(...). The
// check resolves the object handle to its class type; when the type cannot be
// resolved it stays silent, so the error is reported only when the absence of
// the block is certain.
static void CheckNamedConstraintModeExists(
    const Stmt* s,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  const Expr* prefix = MatchNamedConstraintModePrefix(s);
  if (!prefix) return;

  auto obj_name = prefix->lhs->text;
  auto constraint_name = prefix->rhs->text;

  auto it = var_types.find(obj_name);
  if (it == var_types.end()) return;
  const auto* cls = FindClassDecl(it->second, unit);
  if (!cls || cls->is_interface) return;

  if (ClassHierarchyHasConstraint(cls, constraint_name, unit)) return;

  diag.Error(prefix->rhs->range.start,
             std::format("constraint '{}' does not exist in the hierarchy of "
                         "class '{}'",
                         constraint_name, it->second),
             Subclause("18.9"));
}

// 18.8, 18.9: matches a call of the no-name form -- `handle.rand_mode()` or
// `handle.constraint_mode()`, whose receiver is the object handle itself
// rather than a named random variable or constraint block -- that carries no
// argument, on a handle whose class type is known and is not an interface
// class. Returns the method-name expression, which the caller anchors its
// diagnostic at, or nullptr when *s* is not that form. An unresolved receiver
// yields nullptr and so stays silent, mirroring the named-form checks.
static const Expr* MatchUnnamedModeCallWithoutArgument(
    const Stmt* s, std::string_view method,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit) {
  const Expr* call = ExtractCallFromStmt(s);
  if (!call) return nullptr;
  const Expr* callee = call->lhs;
  if (!callee || callee->kind != ExprKind::kMemberAccess) return nullptr;
  if (!callee->rhs || callee->rhs->kind != ExprKind::kIdentifier)
    return nullptr;
  if (callee->rhs->text != method) return nullptr;

  // The named form's receiver is itself a member access (object.name) and is
  // handled elsewhere; only a plain object handle is the no-name form.
  const Expr* recv = callee->lhs;
  if (!recv || recv->kind != ExprKind::kIdentifier) return nullptr;

  auto it = var_types.find(recv->text);
  if (it == var_types.end()) return nullptr;
  const auto* cls = FindClassDecl(it->second, unit);
  if (!cls || cls->is_interface) return nullptr;

  if (!call->args.empty()) return nullptr;
  return callee->rhs;
}

// 18.8: rand_mode() has two forms -- a void form that takes an on/off argument
// (the variable name is optional and, when omitted, the operation applies to
// all random variables) and a nonvoid form that takes no argument and reports
// one named variable's state. Omitting the variable name is only permitted in
// the void (argument-bearing) form, so a call that names no variable AND passes
// no argument matches neither form and is illegal.
static void CheckUnnamedRandModeHasArgument(
    const Stmt* s,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  const Expr* method =
      MatchUnnamedModeCallWithoutArgument(s, "rand_mode", var_types, unit);
  if (!method) return;
  diag.Error(method->range.start,
             "rand_mode() called with no variable name requires an on/off "
             "argument; the no-argument query form must name a random "
             "variable",
             Subclause("18.8"));
}

// 18.9: constraint_mode() has two forms -- a void form that takes an on/off
// argument (the constraint name is optional and, when omitted, the operation
// applies to all constraints) and a nonvoid form that takes no argument and
// reports one named block's state. Omitting the constraint name is only
// permitted in the void (argument-bearing) form, so a call that names no
// constraint AND passes no argument matches neither form and is illegal.
static void CheckUnnamedConstraintModeHasArgument(
    const Stmt* s,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  const Expr* method = MatchUnnamedModeCallWithoutArgument(s, "constraint_mode",
                                                           var_types, unit);
  if (!method) return;
  diag.Error(method->range.start,
             "constraint_mode() called with no constraint name requires an "
             "on/off argument; the no-argument query form must name a "
             "constraint block",
             Subclause("18.9"));
}

// Returns true when *e* is a bare `new` object-construction call (the
// scope-less form written simply as `new` or `new(args)`), as opposed to a
// typed constructor call such as `Derived::new`.
static bool IsBareNewCall(const Expr* e) {
  return e && e->kind == ExprKind::kCall && e->text == "new";
}

// §8.21 and §8.26.5: no object of an abstract class or an interface class is
// constructed directly; the class `name` names is reported at `loc` where it
// is one of the two. The rule is on the source, so it is reported here whether
// or not the construction ever runs.
static void ReportUnconstructibleClass(std::string_view name, SourceLoc loc,
                                       const CompilationUnit* unit,
                                       DiagEngine& diag) {
  const auto* cls = FindClassDecl(name, unit);
  if (cls == nullptr) return;
  if (cls->is_interface) {
    diag.Error(loc,
               std::format("cannot construct object of interface class '{}'",
                           cls->name),
               Subclause("8.26.5"));
  } else if (cls->is_virtual) {
    diag.Error(loc,
               std::format("cannot construct object of abstract class '{}'",
                           cls->name),
               Subclause("8.21"));
  }
}

// §9.7, §8.21 and §8.26.5: the construction `init` of an object for a handle
// declared `type`, written at `loc` as a declaration's initializer or an
// assignment's right-hand side. A typed constructor call, `B::new`, builds an
// object of the class it names; a bare `new` builds one of `type`, which §G.6
// gives no constructor where it is the built-in process class (§9.7), and
// which is reported where it is abstract or an interface class.
static void CheckConstruction(std::string_view type, const Expr* init,
                              SourceLoc loc, const CompilationUnit* unit,
                              DiagEngine& diag) {
  if (!IsBareNewCall(init)) {
    ReportUnconstructibleClass(TypedConstructorScopeType(init), loc, unit,
                               diag);
    return;
  }
  const std::optional<StdPackageMember> kStd = StdPackageMemberNamed(type);
  if (kStd && !StdClassPrototype(*kStd).empty() &&
      !StdClassHasConstructor(*kStd)) {
    diag.Error(loc,
               std::format("cannot construct a {} object with 'new'", type),
               Subclause("9.7"));
    return;
  }
  ReportUnconstructibleClass(type, loc, unit, diag);
}

// The class type a declaration of `type` with the unpacked dimensions `dims`
// gives one handle of; empty for an array of handles, `process job[]`, whose
// `new [N]` initializer is §7.5.1's dynamic_array_new, sizing the array, and
// constructs no object.
static std::string_view DeclaredHandleType(const DataType& type,
                                           const std::vector<Expr*>& dims) {
  return dims.empty() ? type.type_name : std::string_view();
}

// The construction a handle assignment writes, `p = new;` or `h = B::new;`.
static void CheckNewOnUnconstructibleHandle(
    const Stmt* s,
    const std::unordered_map<std::string_view, std::string_view>&
        class_var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  auto lt = class_var_types.find(ExprIdent(s->lhs));
  if (lt == class_var_types.end()) return;
  CheckConstruction(lt->second, s->rhs, s->range.start, unit, diag);
}

// §8.8: a typed constructor call may name a type different from the assignment
// target, but that specified type shall be assignment compatible with the
// target — i.e. the same class or one derived from it. Reject a scope type
// that is an unrelated class.
static void CheckTypedConstructorCompatibility(
    const Stmt* s, const std::unordered_set<std::string_view>& class_names,
    const std::unordered_map<std::string_view, std::string_view>&
        class_var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  auto specified = TypedConstructorScopeType(s->rhs);
  if (specified.empty() || !class_names.count(specified)) return;
  auto lhs_name = ExprIdent(s->lhs);
  auto lt = class_var_types.find(lhs_name);
  if (lt != class_var_types.end() &&
      !IsClassDerivedFrom(specified, lt->second, unit)) {
    diag.Error(s->range.start,
               "typed constructor call type is not assignment compatible "
               "with the target",
               Subclause("8.8"));
  }
}

// §8.8: a typed constructor call used as a declaration initializer (e.g.
// `C c = D::new;`) is an assignment to the declared handle, so the specified
// type shall be assignment compatible with the declared type -- exactly the
// rule the procedural-assignment path enforces via
// CheckTypedConstructorCompatibility. A declaration carries its target type on
// the declaration itself and its source expression in var_init, so the check
// reads those rather than lhs/rhs.
static void CheckTypedConstructorDeclInitCompatibility(
    const Stmt* s, const std::unordered_set<std::string_view>& class_names,
    const CompilationUnit* unit, DiagEngine& diag) {
  auto specified = TypedConstructorScopeType(s->var_init);
  if (specified.empty() || !class_names.count(specified)) return;
  if (!IsClassDerivedFrom(specified, s->var_decl_type.type_name, unit)) {
    diag.Error(s->range.start,
               "typed constructor call type is not assignment compatible "
               "with the target",
               Subclause("8.8"));
  }
}

// §8.8: the same declaration-initializer compatibility rule applies when the
// declaration is a module-scope variable (`C c = D::new;` at module level)
// rather than a block-local one. A module item carries its target type in
// data_type and its initializer in init_expr, and the walk over procedural
// blocks never reaches it, so the module-scope declaration is checked here.
static void CheckTypedConstructorModuleItemCompatibility(
    const ModuleItem* item,
    const std::unordered_set<std::string_view>& class_names,
    const CompilationUnit* unit, DiagEngine& diag) {
  auto specified = TypedConstructorScopeType(item->init_expr);
  if (specified.empty() || !class_names.count(specified)) return;
  if (!IsClassDerivedFrom(specified, item->data_type.type_name, unit)) {
    diag.Error(item->loc,
               "typed constructor call type is not assignment compatible "
               "with the target",
               Subclause("8.8"));
  }
}

// Reject assignment of one class handle to another when the source type is not
// assignment compatible with the target type.
static void CheckClassHandleAssignCompatibility(
    const Stmt* s, const std::unordered_set<std::string_view>& class_var_names,
    const std::unordered_map<std::string_view, std::string_view>&
        class_var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  if (!(s->rhs && IsClassVar(s->rhs, class_var_names))) return;
  auto lhs_name = ExprIdent(s->lhs);
  auto rhs_name = ExprIdent(s->rhs);
  auto lt = class_var_types.find(lhs_name);
  auto rt = class_var_types.find(rhs_name);
  if (lt != class_var_types.end() && rt != class_var_types.end() &&
      !IsClassDerivedFrom(rt->second, lt->second, unit)) {
    diag.Error(s->range.start,
               "class handle assignment requires assignment compatible types",
               Subclause("8.4"));
  }
}

// Returns true when *e* is a literal value (integer/real/time/string/unbased
// unsized) that cannot be assigned to a class object handle.
static bool IsNonClassLiteral(const Expr* e) {
  return e && (e->kind == ExprKind::kIntegerLiteral ||
               e->kind == ExprKind::kRealLiteral ||
               e->kind == ExprKind::kTimeLiteral ||
               e->kind == ExprKind::kStringLiteral ||
               e->kind == ExprKind::kUnbasedUnsizedLiteral);
}

// Reject a compound assignment (e.g. +=, |=) whose target is a class handle.
static void CheckCompoundAssignOnClassHandle(const Stmt* s, DiagEngine& diag) {
  if (s->rhs && s->rhs->kind == ExprKind::kBinary &&
      IsCompoundAssignOp(s->rhs->op)) {
    diag.Error(s->range.start,
               "operator is not allowed on class object handles",
               Subclause("8.4"));
  }
}

// Reject assigning a literal (non-class) value to a class object handle.
static void CheckNonClassLiteralAssign(const Stmt* s, DiagEngine& diag) {
  if (IsNonClassLiteral(s->rhs)) {
    diag.Error(s->range.start,
               "cannot assign non-class value to class object handle",
               Subclause("8.4"));
  }
}

// The elaborated class environment a statement is validated against: the set of
// declared class type names, the set of class-handle variable names in scope,
// the map from each such variable to its declared class type, and the
// compilation unit used to resolve class declarations. These read-only lookup
// structures together describe one entity — the class-handle elaboration
// context referenced throughout §8.8/§18.9 handle and constructor checks.
namespace {
struct ClassHandleContext {
  const std::unordered_set<std::string_view>& class_names;
  const std::unordered_set<std::string_view>& class_var_names;
  const std::unordered_map<std::string_view, std::string_view>& class_var_types;
  const CompilationUnit* unit;
};
}  // namespace

// Runs every assignment-target check that applies when a blocking/nonblocking
// assignment writes a class-handle variable.
static void CheckClassHandleAssignTarget(const Stmt* s,
                                         const ClassHandleContext& ctx,
                                         DiagEngine& diag) {
  CheckCompoundAssignOnClassHandle(s, diag);
  CheckNewOnUnconstructibleHandle(s, ctx.class_var_types, ctx.unit, diag);
  CheckTypedConstructorCompatibility(s, ctx.class_names, ctx.class_var_types,
                                     ctx.unit, diag);
  CheckClassHandleAssignCompatibility(s, ctx.class_var_names,
                                      ctx.class_var_types, ctx.unit, diag);
  CheckNonClassLiteralAssign(s, diag);
}

void ElaboratorClassRules::WalkStmtsForClassHandleOps(const Stmt* s) {
  if (!s) return;

  if (s->kind == StmtKind::kVarDecl &&
      s->var_decl_type.kind == DataTypeKind::kNamed &&
      class_names_.count(s->var_decl_type.type_name)) {
    // §7.4.2 (printed pages 153-154) and §7.5: a block item declaration with
    // an unpacked dimension, `C arr[2]` or `C d[]`, is an array whose
    // elements are handles, and a select of it is an element, not §8.4's
    // (printed 181) bit-select of a handle, as ValidateVarDeclTypes already
    // reads a module-scope declaration. Every block-declared variable of a
    // class type was taken for one handle, so `arr[1] = new` and `arr[1].v`
    // in an initial block were reported.
    if (s->var_unpacked_dims.empty()) class_var_names_.insert(s->var_name);
    class_var_types_[s->var_name] = s->var_decl_type.type_name;
    CheckTypedConstructorDeclInitCompatibility(s, class_names_, unit_, diag_);
    CheckConstruction(
        DeclaredHandleType(s->var_decl_type, s->var_unpacked_dims), s->var_init,
        s->range.start, unit_, diag_);
  }

  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->lhs && IsClassVar(s->lhs, class_var_names_)) {
    ClassHandleContext ctx{class_names_, class_var_names_, class_var_types_,
                           unit_};
    CheckClassHandleAssignTarget(s, ctx, diag_);
  }

  if ((s->kind == StmtKind::kBlockingAssign ||
       s->kind == StmtKind::kNonblockingAssign) &&
      s->lhs && s->lhs->kind == ExprKind::kIdentifier &&
      !IsClassVar(s->lhs, class_var_names_) && s->rhs &&
      IsClassVar(s->rhs, class_var_names_)) {
    diag_.Error(s->range.start,
                "cannot assign class object handle to a non-class variable",
                Subclause("8.4"));
  }

  CheckInterfaceHandleRandConstraintMode(s, class_var_types_, unit_, diag_);

  CheckNamedConstraintModeExists(s, class_var_types_, unit_, diag_);

  CheckUnnamedConstraintModeHasArgument(s, class_var_types_, unit_, diag_);

  CheckRandModeVariableNames(ExtractCallFromStmt(s), class_var_types_, unit_,
                             diag_);

  CheckUnnamedRandModeHasArgument(s, class_var_types_, unit_, diag_);

  const ClassHandleTables kTables{class_var_names_, class_var_types_,
                                  var_types_, unit_};
  CheckClassHandleExpr(s->rhs, kTables, diag_);
  CheckClassHandleExpr(s->expr, kTables, diag_);
  CheckClassHandleExpr(s->condition, kTables, diag_);
  // §8.4 states which operations an object handle admits and §8.26.9 which
  // ones an interface class handle admits, and neither names a statement the
  // rules are suspended in, so this descends every link ForEachChildStmt in
  // elaborator_validate_internal.h names and names no link itself. It wrote out
  // six of the thirteen, so `fork r = a + 1; join` and `assert (1) else r = a +
  // 1;` performed arithmetic on a handle where nothing looked, and a handle
  // declared in one of those seven links never entered class_var_names_ either,
  // which left every later operation on it unchecked as well.
  // §6.21 says of a declaration in a block that such variables are visible to
  // the block and every block nested below it, so the binding a declaration
  // makes ends where its block does. The two tables are members written
  // straight into, and nothing unwound them at a block's end: a handle declared
  // in one procedural block rebound its name for the rest of the module, and
  // every later check reading the tables read the wrong class.
  //
  // The cost ran both ways. A handle shadowed by a narrower class lost the
  // reports its own class earns -- §8.18's local member reached from outside
  // went unreported -- and one shadowed by a stricter class gained reports it
  // does not earn.
  //
  // A block and a fork are the scopes §6.21 names, so the tables are put back
  // as they were when the walk leaves one. Every other statement's children are
  // in the scope the statement itself stands in, and a declaration among them
  // is a declaration of that scope.
  bool opens_scope = s->kind == StmtKind::kBlock || s->kind == StmtKind::kFork;
  auto outer_names =
      opens_scope ? class_var_names_ : decltype(class_var_names_)();
  auto outer_types =
      opens_scope ? class_var_types_ : decltype(class_var_types_)();
  ForEachChildStmt(
      s, [this](Stmt* const& sub) { WalkStmtsForClassHandleOps(sub); });
  if (opens_scope) {
    class_var_names_ = std::move(outer_names);
    class_var_types_ = std::move(outer_types);
  }
}

void ElaboratorClassRules::ValidateClassHandleOps(const ModuleDecl* decl) {
  // Block-local class handles are not seeded into class_var_names_ (only
  // module-scope handles are); they are collected during the walk itself
  // (WalkStmtsForClassHandleOps records each kVarDecl in source order before
  // reaching later assignments). Guarding on class_var_names_ would skip the
  // walk entirely when every handle is declared inside a procedural block, so
  // guard on class_names_ instead, mirroring ValidateLocalProtectedAccess.
  if (class_names_.empty()) return;
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl && item->init_expr &&
        item->data_type.kind == DataTypeKind::kNamed &&
        class_names_.count(item->data_type.type_name)) {
      CheckTypedConstructorModuleItemCompatibility(item, class_names_, unit_,
                                                   diag_);
      CheckConstruction(
          DeclaredHandleType(item->data_type, item->unpacked_dims),
          item->init_expr, item->loc, unit_, diag_);
    }
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForClassHandleOps(item->body);
    }
  }
  // §8.4 names no scope its rules are suspended in, so a task's or a
  // function's body, and a class method's, is held to them as a procedure's.
  WalkSubroutinesForClassHandleOps(decl->items);
}

void ElaboratorClassRules::ValidateClassHandleContAssign(
    const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kContAssign) return;
  auto lhs_class =
      item->assign_lhs && IsClassVar(item->assign_lhs, class_var_names_);
  auto rhs_class =
      item->assign_rhs && IsClassVar(item->assign_rhs, class_var_names_);
  if (lhs_class || rhs_class) {
    diag_.Error(item->loc,
                "class object handle cannot be used in continuous assignment",
                Subclause("10.3"));
  }
}

}  // namespace delta
