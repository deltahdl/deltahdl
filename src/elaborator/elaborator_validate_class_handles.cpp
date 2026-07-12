#include <format>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"

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

bool IsClassDerivedFrom(std::string_view a, std::string_view b,
                        const CompilationUnit* unit) {
  if (a == b) return true;
  for (const auto* cls = FindClassDecl(a, unit); cls;
       cls = cls->base_class.empty() ? nullptr
                                     : FindClassDecl(cls->base_class, unit)) {
    if (cls->base_class == b) return true;
    if (AnyInterfaceDerivedFrom(cls, b, unit)) return true;
  }
  return false;
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

// Validates the operands of a binary expression that involves at least one
// class-handle variable: rejects disallowed operators and, for comparisons of
// two handles, requires assignment-compatible types.
static void CheckClassHandleBinary(
    const Expr* e, const std::unordered_set<std::string_view>& class_vars,
    const std::unordered_map<std::string_view, std::string_view>&
        class_var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  bool lhs_class = e->lhs && IsClassVar(e->lhs, class_vars);
  bool rhs_class = e->rhs && IsClassVar(e->rhs, class_vars);
  if ((lhs_class || rhs_class) && !IsAllowedClassBinaryOp(e->op)) {
    diag.Error(e->range.start,
               "operator is not allowed on class object handles");
  }

  if (lhs_class && rhs_class && IsAllowedClassBinaryOp(e->op)) {
    auto lhs_name = ExprIdent(e->lhs);
    auto rhs_name = ExprIdent(e->rhs);
    auto lt = class_var_types.find(lhs_name);
    auto rt = class_var_types.find(rhs_name);
    if (lt != class_var_types.end() && rt != class_var_types.end() &&
        !AreClassTypesComparable(lt->second, rt->second, unit)) {
      diag.Error(e->range.start,
                 "class handle comparison requires assignment compatible "
                 "types");
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
               "cannot cast class object handle to a non-class type");
  }

  if (!e->text.empty() && FindClassDecl(e->text, unit) != nullptr && e->lhs &&
      !IsClassVar(e->lhs, class_vars) &&
      (e->lhs->kind != ExprKind::kIdentifier || e->lhs->text != "null")) {
    diag.Error(e->range.start, "cannot cast non-class value to a class type");
  }
}

static void CheckClassHandleExpr(
    const Expr* e, const std::unordered_set<std::string_view>& class_vars,
    const std::unordered_map<std::string_view, std::string_view>&
        class_var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  if (!e) return;

  if (e->kind == ExprKind::kBinary) {
    CheckClassHandleBinary(e, class_vars, class_var_types, unit, diag);
  }

  if (e->kind == ExprKind::kUnary && IsClassVar(e->lhs, class_vars)) {
    diag.Error(e->range.start,
               "operator is not allowed on class object handles");
  }

  if (e->kind == ExprKind::kPostfixUnary && IsClassVar(e->lhs, class_vars)) {
    diag.Error(e->range.start,
               "operator is not allowed on class object handles");
  }

  if (e->kind == ExprKind::kSelect && e->base &&
      IsClassVar(e->base, class_vars)) {
    diag.Error(e->range.start, "bit-select on class object handle is illegal");
  }

  if (e->kind == ExprKind::kCast) {
    CheckClassHandleCast(e, class_vars, unit, diag);
  }

  CheckClassHandleExpr(e->lhs, class_vars, class_var_types, unit, diag);
  CheckClassHandleExpr(e->rhs, class_vars, class_var_types, unit, diag);
  CheckClassHandleExpr(e->base, class_vars, class_var_types, unit, diag);
  CheckClassHandleExpr(e->index, class_vars, class_var_types, unit, diag);
  CheckClassHandleExpr(e->condition, class_vars, class_var_types, unit, diag);
  CheckClassHandleExpr(e->true_expr, class_vars, class_var_types, unit, diag);
  CheckClassHandleExpr(e->false_expr, class_vars, class_var_types, unit, diag);
  for (const auto* elem : e->elements) {
    CheckClassHandleExpr(elem, class_vars, class_var_types, unit, diag);
  }
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
                         method_name, var_name));
}

// Returns true when *cls* or any of its base classes declares a constraint
// block named *constraint_name*.
static bool ClassHierarchyHasConstraint(const ClassDecl* cls,
                                        std::string_view constraint_name,
                                        const CompilationUnit* unit) {
  for (const auto* c = cls; c; c = c->base_class.empty()
                                       ? nullptr
                                       : FindClassDecl(c->base_class, unit)) {
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

// 18.9: the constraint named in a constraint_mode() call shall be a constraint
// block that exists in the object's class hierarchy; naming one that does not
// exist is a compile-time error. This applies only to the named form
// obj.constraint_id.constraint_mode(...). The check resolves the object handle
// to its class type; when the type cannot be resolved it stays silent, so the
// error is reported only when the absence of the block is certain.
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
                         constraint_name, it->second));
}

// 18.8: report whether *cls* or any of its base classes declares a data member
// named *var_name*, distinguishing a random variable (rand/randc) from any
// other member. 'found' is set when a member of that name exists at all;
// 'is_rand' when it is declared rand or randc. The most-derived declaration of
// the name decides, matching the visibility a rand_mode() call resolves.
static void ClassHierarchyRandVariableStatus(const ClassDecl* cls,
                                             std::string_view var_name,
                                             const CompilationUnit* unit,
                                             bool& found, bool& is_rand) {
  found = false;
  is_rand = false;
  for (const auto* c = cls; c; c = c->base_class.empty()
                                       ? nullptr
                                       : FindClassDecl(c->base_class, unit)) {
    for (const auto* m : c->members) {
      if (m->kind == ClassMemberKind::kProperty && m->name == var_name) {
        found = true;
        is_rand = m->is_rand || m->is_randc;
        return;  // most-derived declaration of the name wins
      }
    }
  }
}

// Matches the named form obj.random_variable.rand_mode(...) of a call
// statement. On success returns the prefix member access (whose left side is
// the object handle identifier and whose right side is the variable name), and
// nullptr otherwise -- including for the no-name form obj.rand_mode(...), whose
// receiver is a plain identifier rather than a member access.
static const Expr* MatchNamedRandModePrefix(const Stmt* s) {
  const Expr* call = ExtractCallFromStmt(s);
  if (!call) return nullptr;

  const Expr* callee = call->lhs;
  if (!callee || callee->kind != ExprKind::kMemberAccess) return nullptr;
  if (!callee->rhs || callee->rhs->kind != ExprKind::kIdentifier)
    return nullptr;
  if (callee->rhs->text != "rand_mode") return nullptr;

  const Expr* prefix = callee->lhs;
  if (!prefix || prefix->kind != ExprKind::kMemberAccess) return nullptr;
  if (!prefix->lhs || prefix->lhs->kind != ExprKind::kIdentifier)
    return nullptr;
  if (!prefix->rhs || prefix->rhs->kind != ExprKind::kIdentifier)
    return nullptr;
  return prefix;
}

// 18.8: a compiler error shall be issued if the variable named in a rand_mode()
// call does not exist within the object's class hierarchy, or exists but is not
// declared rand or randc. This applies to the named form
// obj.random_variable.rand_mode(...); the no-name form (which applies to every
// random variable) names nothing to validate. The check resolves the object
// handle to its class type and stays silent when that type is unknown, so the
// error is reported only when the variable's absence (or non-random status) is
// certain.
static void CheckNamedRandModeVariableExists(
    const Stmt* s,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  const Expr* prefix = MatchNamedRandModePrefix(s);
  if (!prefix) return;

  auto obj_name = prefix->lhs->text;
  auto var_name = prefix->rhs->text;

  auto it = var_types.find(obj_name);
  if (it == var_types.end()) return;
  const auto* cls = FindClassDecl(it->second, unit);
  if (!cls || cls->is_interface) return;

  bool found = false;
  bool is_rand = false;
  ClassHierarchyRandVariableStatus(cls, var_name, unit, found, is_rand);
  if (is_rand) return;

  if (!found) {
    diag.Error(prefix->rhs->range.start,
               std::format("random variable '{}' does not exist in the "
                           "hierarchy of class '{}'",
                           var_name, it->second));
  } else {
    diag.Error(prefix->rhs->range.start,
               std::format("'{}' is not declared rand or randc, so rand_mode() "
                           "cannot be applied to it",
                           var_name));
  }
}

// 18.8: rand_mode() has two forms -- a void form that takes an on/off argument
// (the variable name is optional and, when omitted, the operation applies to
// all random variables) and a nonvoid form that takes no argument and reports
// one named variable's state. Omitting the variable name is only permitted in
// the void (argument-bearing) form, so a call that names no variable AND passes
// no argument matches neither form and is illegal. Detect the no-name form --
// the receiver of rand_mode is the object handle itself, not
// object.random_variable -- with an empty argument list, on a handle whose
// class type is known.
static void CheckUnnamedRandModeHasArgument(
    const Stmt* s,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  const Expr* call = ExtractCallFromStmt(s);
  if (!call) return;
  const Expr* callee = call->lhs;
  if (!callee || callee->kind != ExprKind::kMemberAccess) return;
  if (!callee->rhs || callee->rhs->kind != ExprKind::kIdentifier) return;
  if (callee->rhs->text != "rand_mode") return;

  // The no-name form's receiver is the plain object handle; the named form's
  // receiver is a member access (object.random_variable) and is handled
  // elsewhere.
  const Expr* recv = callee->lhs;
  if (!recv || recv->kind != ExprKind::kIdentifier) return;

  // Only diagnose when the receiver is a known class handle, mirroring the
  // named-form check: an unresolved receiver stays silent.
  auto it = var_types.find(recv->text);
  if (it == var_types.end()) return;
  const auto* cls = FindClassDecl(it->second, unit);
  if (!cls || cls->is_interface) return;

  if (!call->args.empty()) return;

  diag.Error(callee->rhs->range.start,
             "rand_mode() called with no variable name requires an on/off "
             "argument; the no-argument query form must name a random "
             "variable");
}

// 18.9: constraint_mode() has two forms -- a void form that takes an on/off
// argument (the constraint name is optional and, when omitted, the operation
// applies to all constraints) and a nonvoid form that takes no argument and
// reports one named block's state. Omitting the constraint name is only
// permitted in the void (argument-bearing) form, so a call that names no
// constraint AND passes no argument matches neither form and is illegal. Detect
// the no-name form -- the receiver of constraint_mode is the object handle
// itself, not object.constraint_id -- with an empty argument list, on a handle
// whose class type is known.
static void CheckUnnamedConstraintModeHasArgument(
    const Stmt* s,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  const Expr* call = ExtractCallFromStmt(s);
  if (!call) return;
  const Expr* callee = call->lhs;
  if (!callee || callee->kind != ExprKind::kMemberAccess) return;
  if (!callee->rhs || callee->rhs->kind != ExprKind::kIdentifier) return;
  if (callee->rhs->text != "constraint_mode") return;

  // The no-name form's receiver is the plain object handle; the named form's
  // receiver is a member access (object.constraint_id) and is handled
  // elsewhere.
  const Expr* recv = callee->lhs;
  if (!recv || recv->kind != ExprKind::kIdentifier) return;

  // Only diagnose when the receiver is a known class handle, mirroring the
  // named-form check: an unresolved receiver stays silent.
  auto it = var_types.find(recv->text);
  if (it == var_types.end()) return;
  const auto* cls = FindClassDecl(it->second, unit);
  if (!cls || cls->is_interface) return;

  if (!call->args.empty()) return;

  diag.Error(callee->rhs->range.start,
             "constraint_mode() called with no constraint name requires an "
             "on/off argument; the no-argument query form must name a "
             "constraint block");
}

// Reject a 'new' constructor call assigned to a handle whose declared type
// cannot be constructed: the built-in 'process' class and interface classes.
static void CheckNewOnUnconstructibleHandle(
    const Stmt* s,
    const std::unordered_map<std::string_view, std::string_view>&
        class_var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  if (!s->rhs || s->rhs->kind != ExprKind::kCall || s->rhs->text != "new") {
    return;
  }
  auto lhs_name = ExprIdent(s->lhs);
  auto lt = class_var_types.find(lhs_name);
  if (lt == class_var_types.end()) return;
  if (lt->second == "process") {
    diag.Error(s->range.start, "cannot construct a process object with 'new'");
    return;
  }
  const auto* cls = FindClassDecl(lt->second, unit);
  if (cls && cls->is_interface) {
    diag.Error(s->range.start,
               std::format("cannot construct object of interface class '{}'",
                           cls->name));
  }
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
               "with the target");
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
               "class handle assignment requires assignment compatible types");
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
               "operator is not allowed on class object handles");
  }
}

// Reject assigning a literal (non-class) value to a class object handle.
static void CheckNonClassLiteralAssign(const Stmt* s, DiagEngine& diag) {
  if (IsNonClassLiteral(s->rhs)) {
    diag.Error(s->range.start,
               "cannot assign non-class value to class object handle");
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

void Elaborator::WalkStmtsForClassHandleOps(const Stmt* s) {
  if (!s) return;

  if (s->kind == StmtKind::kVarDecl &&
      s->var_decl_type.kind == DataTypeKind::kNamed &&
      class_names_.count(s->var_decl_type.type_name)) {
    class_var_names_.insert(s->var_name);
    class_var_types_[s->var_name] = s->var_decl_type.type_name;
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
                "cannot assign class object handle to a non-class variable");
  }

  CheckInterfaceHandleRandConstraintMode(s, class_var_types_, unit_, diag_);

  CheckNamedConstraintModeExists(s, class_var_types_, unit_, diag_);

  CheckUnnamedConstraintModeHasArgument(s, class_var_types_, unit_, diag_);

  CheckNamedRandModeVariableExists(s, class_var_types_, unit_, diag_);

  CheckUnnamedRandModeHasArgument(s, class_var_types_, unit_, diag_);

  CheckClassHandleExpr(s->rhs, class_var_names_, class_var_types_, unit_,
                       diag_);
  CheckClassHandleExpr(s->expr, class_var_names_, class_var_types_, unit_,
                       diag_);
  CheckClassHandleExpr(s->condition, class_var_names_, class_var_types_, unit_,
                       diag_);
  for (auto* sub : s->stmts) WalkStmtsForClassHandleOps(sub);
  WalkStmtsForClassHandleOps(s->then_branch);
  WalkStmtsForClassHandleOps(s->else_branch);
  WalkStmtsForClassHandleOps(s->body);
  WalkStmtsForClassHandleOps(s->for_body);
  for (auto& ci : s->case_items) WalkStmtsForClassHandleOps(ci.body);
}

void Elaborator::ValidateClassHandleOps(const ModuleDecl* decl) {
  // Block-local class handles are not seeded into class_var_names_ (only
  // module-scope handles are); they are collected during the walk itself
  // (WalkStmtsForClassHandleOps records each kVarDecl in source order before
  // reaching later assignments). Guarding on class_var_names_ would skip the
  // walk entirely when every handle is declared inside a procedural block, so
  // guard on class_names_ instead, mirroring ValidateLocalProtectedAccess.
  if (class_names_.empty()) return;
  for (const auto* item : decl->items) {
    bool is_proc = item->kind == ModuleItemKind::kAlwaysBlock ||
                   item->kind == ModuleItemKind::kInitialBlock;
    if (is_proc && item->body) {
      WalkStmtsForClassHandleOps(item->body);
    }
  }
}

void Elaborator::ValidateClassHandleContAssign(const ModuleItem* item) {
  if (item->kind != ModuleItemKind::kContAssign) return;
  auto lhs_class =
      item->assign_lhs && IsClassVar(item->assign_lhs, class_var_names_);
  auto rhs_class =
      item->assign_rhs && IsClassVar(item->assign_rhs, class_var_names_);
  if (lhs_class || rhs_class) {
    diag_.Error(item->loc,
                "class object handle cannot be used in continuous assignment");
  }
}

}  // namespace delta
