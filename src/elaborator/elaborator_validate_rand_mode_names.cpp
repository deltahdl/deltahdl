#include <format>
#include <string_view>
#include <unordered_map>

#include "common/diagnostic.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

static const ClassMember* FindHierarchyProperty(const ClassDecl* cls,
                                                std::string_view var_name,
                                                const CompilationUnit* unit) {
  for (const auto* c = cls; c; c = FindBaseClass(c, unit)) {
    for (const auto* m : c->members) {
      if (m->kind == ClassMemberKind::kProperty && m->name == var_name)
        return m;
    }
  }
  return nullptr;
}

static const Expr* MatchNamedRandModePrefix(const Expr& call) {
  const Expr* callee = call.lhs;
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

static void CheckRandModeQueryIsSingular(const Expr* prefix, const Expr& call,
                                         const ClassMember& var,
                                         DiagEngine& diag) {
  if (!call.args.empty() || var.unpacked_dims.empty()) return;
  diag.Error(prefix->rhs->range.start,
             std::format("rand_mode() with no argument queries one variable, "
                         "so the unpacked array '{}' needs one element "
                         "selected by its index",
                         prefix->rhs->text),
             Subclause("18.8"));
}

static void CheckNamedRandModeVariableExists(
    const Expr& call,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  const Expr* prefix = MatchNamedRandModePrefix(call);
  if (!prefix) return;

  auto obj_name = prefix->lhs->text;
  auto var_name = prefix->rhs->text;

  auto it = var_types.find(obj_name);
  if (it == var_types.end()) return;
  const auto* cls = FindClassDecl(it->second, unit);
  if (!cls || cls->is_interface) return;

  const ClassMember* var = FindHierarchyProperty(cls, var_name, unit);
  if (var != nullptr && (var->is_rand || var->is_randc)) {
    CheckRandModeQueryIsSingular(prefix, call, *var, diag);
    return;
  }

  if (var == nullptr) {
    diag.Error(prefix->rhs->range.start,
               std::format("random variable '{}' does not exist in the "
                           "hierarchy of class '{}'",
                           var_name, it->second),
               Subclause("18.8"));
  } else {
    diag.Error(prefix->rhs->range.start,
               std::format("'{}' is not declared rand or randc, so rand_mode() "
                           "cannot be applied to it",
                           var_name),
               Subclause("18.8"));
  }
}

static const Expr* MatchRandModeMemberPath(const Expr& call) {
  const Expr* callee = call.lhs;
  if (callee == nullptr || callee->kind != ExprKind::kMemberAccess ||
      callee->rhs->text != "rand_mode") {
    return nullptr;
  }
  const Expr* path = callee->lhs;
  if (path->kind != ExprKind::kMemberAccess || path->is_scope_resolution ||
      path->lhs->kind != ExprKind::kMemberAccess ||
      path->lhs->is_scope_resolution ||
      path->lhs->lhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  return path;
}

static void CheckRandModeStructMember(
    const Expr& call,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  const Expr* path = MatchRandModeMemberPath(call);
  if (path == nullptr) return;
  auto it = var_types.find(path->lhs->lhs->text);
  if (it == var_types.end()) return;
  const auto* cls = FindClassDecl(it->second, unit);
  if (cls == nullptr) return;
  const ClassMember* var =
      FindHierarchyProperty(cls, path->lhs->rhs->text, unit);
  if (var == nullptr || var->data_type.struct_members.empty()) return;
  std::string_view member = path->rhs->text;
  for (const StructMember& field : var->data_type.struct_members) {
    if (field.name != member) continue;
    if (field.is_rand || field.is_randc) return;
    diag.Error(path->rhs->range.start,
               std::format("member '{}' of the structure '{}' is not declared "
                           "rand or randc, so rand_mode() cannot be applied "
                           "to it",
                           member, var->name),
               Subclause("18.8"));
    return;
  }
  diag.Error(
      path->rhs->range.start,
      std::format("the structure '{}' has no member '{}'", var->name, member),
      Subclause("18.8"));
}

void CheckRandModeVariableNames(
    const Expr* call,
    const std::unordered_map<std::string_view, std::string_view>& var_types,
    const CompilationUnit* unit, DiagEngine& diag) {
  if (call == nullptr) return;
  CheckNamedRandModeVariableExists(*call, var_types, unit, diag);
  CheckRandModeStructMember(*call, var_types, unit, diag);
}

}  // namespace delta
