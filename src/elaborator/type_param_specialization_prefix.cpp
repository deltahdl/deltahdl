#include <algorithm>
#include <cstddef>
#include <format>
#include <functional>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/type_param_restriction.h"
#include "elaborator/type_param_scope_prefix.h"
#include "elaborator/type_param_scope_prefix_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

using SelectedNames = std::vector<std::string_view>;

static bool IsSelectedName(std::string_view name, const SelectedNames& names) {
  return std::ranges::find(names, name) != names.end();
}

static bool ExprSelectsThrough(const Expr* e, const SelectedNames& names) {
  if (e == nullptr) return false;
  if (SelectsThroughName(e) && NamesLocalScope(e->lhs) &&
      IsSelectedName(e->lhs->text, names))
    return true;
  return AnyExprChild(
      e, [&](const Expr* child) { return ExprSelectsThrough(child, names); });
}

using ExprVisit = std::function<bool(const Expr*)>;

static bool AnyStmtExpr(const Stmt* s, const ExprVisit& visit) {
  if (s == nullptr) return false;
  bool found = false;
  ForEachChildExpr(s, [&](const Expr* e) {
    if (visit(e)) found = true;
  });
  ForEachChildStmt(s, [&](const Stmt* sub) {
    if (AnyStmtExpr(sub, visit)) found = true;
  });
  return found;
}

static bool AnyMemberExpr(const ClassMember& m, const ExprVisit& visit) {
  if (m.kind == ClassMemberKind::kConstraint)
    return std::ranges::any_of(m.constraint_exprs, visit);
  if (m.method != nullptr)
    return std::ranges::any_of(m.method->func_body_stmts, [&](const Stmt* s) {
      return AnyStmtExpr(s, visit);
    });
  return visit(m.init_expr);
}

static bool TypedefSelectsThrough(const DataType& type,
                                  const SelectedNames& names);

static bool ArgumentsSelectThrough(const std::vector<DataType>& args,
                                   const SelectedNames& names) {
  return std::ranges::any_of(args, [&](const DataType& arg) {
    return TypedefSelectsThrough(arg, names);
  });
}

static bool TypedefSelectsThrough(const DataType& type,
                                  const SelectedNames& names) {
  return (type.outer_scope_names.empty() &&
          IsSelectedName(type.scope_name, names)) ||
         ExprSelectsThrough(type.type_ref_expr, names) ||
         ArgumentsSelectThrough(type.type_params, names);
}

static std::vector<const DataType*> DeclaredTypes(const ClassMember& m) {
  if (m.method == nullptr) return {&m.data_type};
  std::vector<const DataType*> types{&m.method->return_type};
  for (const FunctionArg& arg : m.method->func_args)
    types.push_back(&arg.data_type);
  return types;
}

static bool MemberSelectsThrough(const ClassMember& m,
                                 const SelectedNames& names) {
  if (m.kind == ClassMemberKind::kTypedef)
    return TypedefSelectsThrough(m.typedef_item->typedef_type, names);
  return ExprSelectsThrough(m.data_type.type_ref_expr, names) ||
         std::ranges::any_of(DeclaredTypes(m),
                             [&](const DataType* type) {
                               return ArgumentsSelectThrough(type->type_params,
                                                             names);
                             }) ||
         AnyMemberExpr(
             m, [&](const Expr* e) { return ExprSelectsThrough(e, names); });
}

static bool BaseSelectsThrough(const ClassDecl& cls,
                               const SelectedNames& names) {
  return std::ranges::any_of(BaseArgumentLists(cls),
                             [&](const std::vector<DataType>* args) {
                               return ArgumentsSelectThrough(*args, names);
                             }) ||
         std::ranges::any_of(cls.extends_args, [&](const Expr* arg) {
           return ExprSelectsThrough(arg, names);
         });
}

static SelectedNames NamesBoundTo(const ClassDecl& cls, std::string_view name) {
  SelectedNames names{name};
  for (const ClassMember* m : cls.members) {
    const DataType* bound =
        DeclaresBodyTypeParam(*m) ? &m->typedef_item->typedef_type : nullptr;
    if (bound != nullptr && bound->scope_name.empty() &&
        IsSelectedName(bound->type_name, names))
      names.push_back(m->name);
  }
  return names;
}

static bool DefaultSelectsThrough(const ClassDecl& cls, std::string_view name,
                                  const DataType& written) {
  for (size_t j = 0; j < cls.params.size(); ++j) {
    std::string_view other = cls.params[j].first;
    if (cls.type_param_names.contains(other) &&
        BoundActual(cls, j, other, written) == &cls.param_types[j] &&
        TypedefSelectsThrough(cls.param_types[j], {name}))
      return true;
  }
  return false;
}

static bool BodySelectsThrough(const ClassDecl& cls, std::string_view name) {
  const SelectedNames kNames = NamesBoundTo(cls, name);
  return BaseSelectsThrough(cls, kNames) ||
         std::ranges::any_of(cls.members, [&](const ClassMember* m) {
           return MemberSelectsThrough(*m, kNames);
         });
}

struct TypeOperandBinding {
  const SelectedNames& names;
  const ClassDecl& bound;
  DiagEngine& diag;
};

static void ReportTypeOperand(const Expr* operand,
                              const TypeOperandBinding& binding) {
  if (IsScopeSelection(operand) && NamesLocalScope(operand->lhs) &&
      IsSelectedName(operand->lhs->text, binding.names) &&
      ClassDeclaresType(binding.bound, operand->rhs->text))
    EmitPrefixRestricted(operand->lhs->text, operand->lhs->range.start,
                         binding.diag);
}

static bool ReportTypeOperands(const Expr* e,
                               const TypeOperandBinding& binding) {
  if (e == nullptr || e->kind == ExprKind::kTypeRef) return false;
  if (e->kind == ExprKind::kCast && e->rhs != nullptr)
    ReportTypeOperand(e->rhs, binding);
  if (QueriesAType(e)) ReportTypeOperand(e->args[0], binding);
  ForEachExprChild(
      e, [&](const Expr* child) { ReportTypeOperands(child, binding); });
  return false;
}

static void ReportArgumentTypes(const std::vector<DataType>& args,
                                SourceLoc loc,
                                const TypeOperandBinding& binding) {
  for (const DataType& arg : args) {
    if (arg.outer_scope_names.empty() &&
        IsSelectedName(arg.scope_name, binding.names) &&
        ClassDeclaresType(binding.bound, arg.type_name))
      EmitPrefixRestricted(arg.scope_name, loc, binding.diag);
    ReportArgumentTypes(arg.type_params, loc, binding);
  }
}

static void ReportSpecializationTypeOperands(const ClassDecl& cls,
                                             std::string_view name,
                                             const DataType& actual,
                                             const CompilationUnit* unit,
                                             DiagEngine& diag) {
  const ClassDecl* bound = BoundClass(PrefixBoundOf(&actual), unit);
  if (bound == nullptr) return;
  const SelectedNames kNames = NamesBoundTo(cls, name);
  const TypeOperandBinding kBinding{kNames, *bound, diag};
  for (const std::vector<DataType>* args : BaseArgumentLists(cls))
    ReportArgumentTypes(*args, cls.range.start, kBinding);
  for (const ClassMember* m : cls.members) {
    AnyMemberExpr(
        *m, [&](const Expr* e) { return ReportTypeOperands(e, kBinding); });
    if (m->kind == ClassMemberKind::kTypedef) continue;
    for (const DataType* type : DeclaredTypes(*m))
      ReportArgumentTypes(type->type_params, m->loc, kBinding);
  }
}

static void ReportSpecializationPrefixNotAClass(const DataType& written,
                                                SourceLoc loc,
                                                const CompilationUnit* unit,
                                                DiagEngine& diag) {
  if (written.kind != DataTypeKind::kNamed || !written.scope_name.empty())
    return;
  const ClassDecl* cls = FindClassDecl(written.type_name, unit);
  if (cls == nullptr) return;
  for (size_t i = 0; i < cls->params.size(); ++i) {
    std::string_view name = cls->params[i].first;
    if (!cls->type_param_names.contains(name) ||
        (!BodySelectsThrough(*cls, name) &&
         !DefaultSelectsThrough(*cls, name, written)))
      continue;
    const DataType* actual = BoundActual(*cls, i, name, written);
    ReportSpecializationTypeOperands(*cls, name, *actual, unit, diag);
    if (actual->kind == DataTypeKind::kNamed ||
        actual->kind == DataTypeKind::kImplicit)
      continue;
    diag.ErrorOnce(loc,
                   std::format("type parameter '{}' used as a class scope "
                               "resolution prefix does not resolve to a class",
                               name),
                   Subclause("6.20.3"));
  }
}

void ReportSpecializationBindingErrors(const DataType& written, SourceLoc loc,
                                       const TypeParamRestrictionScope& scope,
                                       DiagEngine& diag) {
  ReportSpecializationPrefixNotAClass(written, loc, scope.unit, diag);
  ReportSpecializationOutsideRestrictions(written, loc, scope, diag);
}

void ReportUnitSpecializations(const TypeParamRestrictionScope& scope,
                               DiagEngine& diag) {
  for (const ModuleItem* item : scope.unit->cu_items) {
    if (item->kind == ModuleItemKind::kTypedef) {
      ReportSpecializationBindingErrors(item->typedef_type, item->loc, scope,
                                        diag);
    } else if (item->kind == ModuleItemKind::kVarDecl) {
      ReportSpecializationBindingErrors(item->data_type, item->loc, scope,
                                        diag);
    }
  }
  for (const ClassDecl* cls : scope.unit->classes) {
    for (const ClassMember* m : cls->members) {
      if (m->kind == ClassMemberKind::kProperty) {
        ReportSpecializationBindingErrors(m->data_type, m->loc, scope, diag);
      } else if (m->kind == ClassMemberKind::kTypedef) {
        ReportSpecializationBindingErrors(m->typedef_item->typedef_type, m->loc,
                                          scope, diag);
      }
    }
  }
}

}  // namespace delta
