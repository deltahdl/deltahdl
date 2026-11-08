#include <cstddef>
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

struct ClassHandleTables {
  const std::unordered_set<std::string_view>& class_vars;
  const std::unordered_map<std::string_view, std::string_view>& class_var_types;
  const std::unordered_map<std::string_view, DataTypeKind>& var_types;
  const std::unordered_set<std::string_view>& keyword_typed_params;
  const CompilationUnit* unit;
};

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

static void CheckClassHandleAssignExpr(const Expr* e,
                                       const ClassHandleTables& t,
                                       bool lhs_class, DiagEngine& diag) {
  if (!lhs_class) {
    if (IsPlainValue(e->lhs, t.var_types)) {
      diag.Error(e->range.start,
                 "cannot assign class object handle to a non-class variable",
                 Subclause("8.4"));
    }
    return;
  }
  if (IsPlainValue(e->rhs, t.var_types)) {
    diag.Error(e->range.start,
               "cannot assign non-class value to class object handle",
               Subclause("8.4"));
    return;
  }
  auto lt = t.class_var_types.find(ExprIdent(e->lhs));
  auto rt = t.class_var_types.find(ExprIdent(e->rhs));
  if (lt != t.class_var_types.end() && rt != t.class_var_types.end() &&
      !IsClassDerivedFrom(rt->second, lt->second, t.unit)) {
    diag.Error(e->range.start,
               "class handle assignment requires assignment compatible types",
               Subclause("8.4"));
  }
}

static void CheckClassHandleBinary(const Expr* e, const ClassHandleTables& t,
                                   DiagEngine& diag) {
  const auto& class_vars = t.class_vars;
  const auto& class_var_types = t.class_var_types;
  const CompilationUnit* unit = t.unit;
  bool lhs_class =
      e->lhs && IsHandleOperand(e->lhs, class_vars, class_var_types, unit);
  bool rhs_class =
      e->rhs && IsHandleOperand(e->rhs, class_vars, class_var_types, unit);
  if (!lhs_class && !rhs_class) return;
  if (e->op == TokenKind::kEq) {
    CheckClassHandleAssignExpr(e, t, lhs_class, diag);
    return;
  }
  if (!IsAllowedClassBinaryOp(e->op)) {
    diag.Error(e->range.start,
               "operator is not allowed on class object handles",
               Subclause("8.4"));
  }

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
      diag.Error(e->range.start,
                 "class handle comparison requires assignment compatible "
                 "types",
                 Subclause("11.4.5"));
    }
  }
}

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

static bool ShareABaseClass(std::string_view a, std::string_view b,
                            const CompilationUnit* unit) {
  if (IsClassDerivedFrom(b, a, unit)) return true;
  for (const auto* cls = FindClassDecl(a, unit); cls != nullptr;
       cls = FindBaseClass(cls, unit)) {
    if (IsClassDerivedFrom(b, cls->name, unit)) return true;
  }
  return false;
}

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

static bool IsBareNewCall(const Expr* e) {
  return e && e->kind == ExprKind::kCall && e->text == "new";
}

static void CheckShallowCopySource(const Expr* e, const ClassHandleTables& t,
                                   DiagEngine& diag) {
  if (!IsBareNewCall(e) || e->lhs == nullptr) return;
  const Expr* src = e->lhs;
  if (src->kind != ExprKind::kIdentifier ||
      t.class_var_types.contains(src->text)) {
    return;
  }
  auto var = t.var_types.find(src->text);
  bool no_handle = var != t.var_types.end()
                       ? var->second != DataTypeKind::kNamed
                       : t.keyword_typed_params.contains(src->text);
  if (!no_handle) return;
  diag.Error(src->range.start,
             std::format("'{}' is no object handle, so 'new' makes no shallow "
                         "copy of it",
                         src->text),
             Subclause("A.2.4"));
}

static void CheckClassHandleExpr(const Expr* e, const ClassHandleTables& t,
                                 DiagEngine& diag) {
  if (!e) return;
  CheckShallowCopySource(e, t, diag);
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

static const Expr* MatchNamedConstraintModePrefix(const Stmt* s) {
  const Expr* call = ExtractCallFromStmt(s);
  if (!call) return nullptr;

  const Expr* callee = call->lhs;
  if (!callee || callee->kind != ExprKind::kMemberAccess) return nullptr;
  if (!callee->rhs || callee->rhs->kind != ExprKind::kIdentifier)
    return nullptr;
  if (callee->rhs->text != "constraint_mode") return nullptr;

  const Expr* prefix = callee->lhs;
  if (!prefix || prefix->kind != ExprKind::kMemberAccess) return nullptr;
  if (!prefix->lhs || prefix->lhs->kind != ExprKind::kIdentifier)
    return nullptr;
  if (!prefix->rhs || prefix->rhs->kind != ExprKind::kIdentifier)
    return nullptr;
  return prefix;
}

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

  const Expr* recv = callee->lhs;
  if (!recv || recv->kind != ExprKind::kIdentifier) return nullptr;

  auto it = var_types.find(recv->text);
  if (it == var_types.end()) return nullptr;
  const auto* cls = FindClassDecl(it->second, unit);
  if (!cls || cls->is_interface) return nullptr;

  if (!call->args.empty()) return nullptr;
  return callee->rhs;
}

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

static std::string_view DeclaredHandleType(const DataType& type,
                                           const std::vector<Expr*>& dims) {
  return dims.empty() ? type.type_name : std::string_view();
}

static void CheckNewOnUnconstructibleHandle(
    const Stmt* s,
    const std::unordered_map<std::string_view, std::string_view>&
        class_var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  auto lt = class_var_types.find(ExprIdent(s->lhs));
  if (lt == class_var_types.end()) return;
  CheckConstruction(lt->second, s->rhs, s->range.start, unit, diag);
}

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

static bool IsNonClassLiteral(const Expr* e) {
  return e && (e->kind == ExprKind::kIntegerLiteral ||
               e->kind == ExprKind::kRealLiteral ||
               e->kind == ExprKind::kTimeLiteral ||
               e->kind == ExprKind::kStringLiteral ||
               e->kind == ExprKind::kUnbasedUnsizedLiteral);
}

static void CheckCompoundAssignOnClassHandle(const Stmt* s, DiagEngine& diag) {
  if (s->rhs && s->rhs->kind == ExprKind::kBinary &&
      IsCompoundAssignOp(s->rhs->op)) {
    diag.Error(s->range.start,
               "operator is not allowed on class object handles",
               Subclause("8.4"));
  }
}

static void CheckNonClassLiteralAssign(const Stmt* s, DiagEngine& diag) {
  if (IsNonClassLiteral(s->rhs)) {
    diag.Error(s->range.start,
               "cannot assign non-class value to class object handle",
               Subclause("8.4"));
  }
}

namespace {
struct ClassHandleContext {
  const std::unordered_set<std::string_view>& class_names;
  const std::unordered_set<std::string_view>& class_var_names;
  const std::unordered_map<std::string_view, std::string_view>& class_var_types;
  const CompilationUnit* unit;
};
}  // namespace

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
  const ClassHandleTables kTables{class_var_names_, class_var_types_,
                                  var_types_, keyword_typed_params_, unit_};

  if (s->kind == StmtKind::kVarDecl &&
      s->var_decl_type.kind == DataTypeKind::kNamed &&
      class_names_.count(s->var_decl_type.type_name)) {
    if (s->var_unpacked_dims.empty()) class_var_names_.insert(s->var_name);
    class_var_types_[s->var_name] = s->var_decl_type.type_name;
    CheckTypedConstructorDeclInitCompatibility(s, class_names_, unit_, diag_);
    CheckConstruction(
        DeclaredHandleType(s->var_decl_type, s->var_unpacked_dims), s->var_init,
        s->range.start, unit_, diag_);
    CheckShallowCopySource(s->var_init, kTables, diag_);
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

  CheckClassHandleExpr(s->rhs, kTables, diag_);
  CheckClassHandleExpr(s->expr, kTables, diag_);
  CheckClassHandleExpr(s->condition, kTables, diag_);
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

static std::unordered_set<std::string_view> KeywordTypedParams(
    const ModuleDecl& decl) {
  auto keyword = [](DataTypeKind k) {
    return k != DataTypeKind::kImplicit && k != DataTypeKind::kNamed &&
           k != DataTypeKind::kVoid;
  };
  std::unordered_set<std::string_view> names;
  for (size_t i = 0; i < decl.params.size(); ++i) {
    std::string_view name = decl.params[i].first;
    if (!decl.type_param_names.contains(name) &&
        keyword(decl.param_types[i].kind)) {
      names.insert(name);
    }
  }
  for (const ModuleItem* item : decl.items) {
    if (item->kind == ModuleItemKind::kParamDecl &&
        keyword(item->data_type.kind)) {
      names.insert(item->name);
    }
  }
  return names;
}

void ElaboratorClassRules::ValidateClassHandleOps(const ModuleDecl* decl) {
  if (class_names_.empty()) return;
  keyword_typed_params_ = KeywordTypedParams(*decl);
  const ClassHandleTables kTables{class_var_names_, class_var_types_,
                                  var_types_, keyword_typed_params_, unit_};
  for (const auto* item : decl->items) {
    if (item->kind == ModuleItemKind::kVarDecl && item->init_expr &&
        item->data_type.kind == DataTypeKind::kNamed &&
        class_names_.count(item->data_type.type_name)) {
      CheckTypedConstructorModuleItemCompatibility(item, class_names_, unit_,
                                                   diag_);
      CheckConstruction(
          DeclaredHandleType(item->data_type, item->unpacked_dims),
          item->init_expr, item->loc, unit_, diag_);
      CheckShallowCopySource(item->init_expr, kTables, diag_);
    }
    bool is_proc = IsProceduralItemKind(item->kind);
    if (is_proc && item->body) {
      WalkStmtsForClassHandleOps(item->body);
    }
  }
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
