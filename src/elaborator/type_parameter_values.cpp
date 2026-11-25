#include "elaborator/type_parameter_values.h"

#include <algorithm>
#include <cstddef>
#include <format>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_items_params.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/scoped_walk.h"
#include "elaborator/type_spelled_by.h"
#include "elaborator/value_scopes.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

std::string_view AssignedParameter(const ClassDecl& cls,
                                   const DataType& assignment,
                                   std::size_t index) {
  if (!assignment.param_arg_name.empty()) return assignment.param_arg_name;
  return index < cls.params.size() ? cls.params[index].first : "";
}

bool AssignsTypeParameter(const ClassDecl* cls, const DataType& assignment,
                          std::size_t index) {
  return cls != nullptr && cls->type_param_names.contains(
                               AssignedParameter(*cls, assignment, index));
}

bool WritesValueArgument(const ClassDecl* cls, const DataType& assignment,
                         std::size_t index) {
  return assignment.type_name.empty() && assignment.type_ref_expr != nullptr &&
         !AssignsTypeParameter(cls, assignment, index);
}

void ReportTypeParamSetToNoType(std::string_view name, SourceLoc loc,
                                DiagEngine& diag) {
  diag.ErrorOnce(loc,
                 std::format("type parameter '{}' can only be set to a data "
                             "type, not a value expression",
                             name),
                 Subclause("6.20.3"));
}

void ReportTypeParamAssignedNoType(const TypeParameterOf& param, SourceLoc loc,
                                   DiagEngine& diag) {
  diag.ErrorOnce(
      loc,
      std::format("parameter value assignment for type parameter '{}' "
                  "of '{}' does not name a type",
                  param.name, param.owner),
      Subclause("6.20.3"));
}

static bool NamesNothing(std::string_view prefix, std::string_view name,
                         const ValueScopes& scopes, const NameScope& scope) {
  if (!prefix.empty()) return scopes.PackageLacks(prefix, name);
  return name != "this" && !scopes.Declares(name, scope);
}

static bool NamesNothing(const Expr* operand, const ValueScopes& scopes,
                         const NameScope& scope) {
  if (operand == nullptr) return false;
  switch (operand->kind) {
    case ExprKind::kIdentifier:
      return NamesNothing(operand->scope_prefix, operand->text, scopes, scope);
    case ExprKind::kMemberAccess:
      return operand->is_scope_resolution &&
             operand->lhs->kind == ExprKind::kIdentifier &&
             NamesNothing(operand->lhs->text, operand->rhs->text, scopes,
                          scope);
    case ExprKind::kUnary:
    case ExprKind::kBinary:
    case ExprKind::kTernary:
    case ExprKind::kConcatenation:
    case ExprKind::kReplicate:
    case ExprKind::kSelect:
      return AnyExprChild(operand, [&](const Expr* child) {
        return NamesNothing(child, scopes, scope);
      });
    default:
      return false;
  }
}

bool WritesNoType(const Expr& written, const ValueScopes& scopes,
                  const NameScope& scope) {
  if (written.kind == ExprKind::kTypeRef)
    return NamesNothing(written.lhs, scopes, scope);
  const DataType kSpelled = TypeSpelledBy(&written);
  if (kSpelled.kind == DataTypeKind::kImplicit) return true;
  return WritesNoType(kSpelled, scopes, scope);
}

bool WritesNoType(const DataType& written, const ValueScopes& scopes,
                  const NameScope& scope) {
  if (written.type_ref_expr != nullptr)
    return WritesNoType(*written.type_ref_expr, scopes, scope);
  return written.kind == DataTypeKind::kNamed &&
         scopes.NamesNoType(written, scope);
}

namespace {

bool IsTypeParameter(const ModuleDecl& decl, std::string_view name) {
  if (decl.type_param_names.contains(name)) return true;
  return std::ranges::any_of(decl.items, [&](const ModuleItem* item) {
    return item->kind == ModuleItemKind::kParamDecl && item->name == name &&
           item->data_type.kind == DataTypeKind::kVoid;
  });
}

class TypeParameterValueWalk : public ScopedWalk {
 public:
  TypeParameterValueWalk(const CompilationUnit& unit, DiagEngine& diag)
      : ScopedWalk(unit), diag_(diag) {}

 private:
  void VisitExpr(const Expr&, const NameScope&) override {}

  void VisitType(const DataType&, SourceLoc, const NameScope&) override {}

  void VisitClass(const ClassDecl& cls, const NameScope& scope) override {
    JudgePorts(cls, scope);
    for (const ClassMember* member : cls.members) {
      if (member->is_param && member->data_type.kind == DataTypeKind::kVoid)
        JudgeValue(*member, member->init_expr, scope);
    }
  }

  void VisitModule(const ModuleDecl& decl, const NameScope& scope) override {
    JudgePorts(decl, scope);
  }

  void VisitParameter(const ModuleItem& param,
                      const NameScope& scope) override {
    if (param.data_type.kind != DataTypeKind::kVoid) return;
    if (param.typedef_type.kind == DataTypeKind::kImplicit &&
        param.typedef_type.type_ref_expr == nullptr) {
      JudgeValue(param, param.init_expr, scope);
    } else if (WritesNoType(param.typedef_type, Scopes(), scope)) {
      ReportTypeParamSetToNoType(param.name, param.loc, diag_);
    }
  }

  void VisitInstance(const ModuleItem& instance,
                     const NameScope& scope) override {
    const ModuleDecl* decl =
        Scopes().ModuleDeclared(instance.inst_module, scope);
    if (decl == nullptr) return;
    const std::vector<std::string_view> kOrdered = OverridableParamNames(decl);
    for (std::size_t i = 0; i < instance.inst_params.size(); ++i) {
      const auto& [name, value] = instance.inst_params[i];
      if (value == nullptr) continue;
      if (name.empty() && i >= kOrdered.size()) break;
      const std::string_view kName = name.empty() ? kOrdered[i] : name;
      if (IsTypeParameter(*decl, kName) &&
          WritesNoType(*value, Scopes(), scope)) {
        ReportTypeParamAssignedNoType({kName, decl->name}, value->range.start,
                                      diag_);
      }
    }
  }

  template <typename Decl>
  void JudgePorts(const Decl& decl, const NameScope& scope) {
    for (std::size_t i = 0; i < decl.params.size(); ++i) {
      const std::string_view kName = decl.params[i].first;
      if (decl.type_param_names.contains(kName) &&
          WritesNoType(decl.param_types[i], Scopes(), scope)) {
        ReportTypeParamSetToNoType(kName, decl.param_port_locs[i], diag_);
      }
    }
  }

  template <typename Param>
  void JudgeValue(const Param& param, const Expr* value,
                  const NameScope& scope) {
    if (value != nullptr && WritesNoType(*value, Scopes(), scope))
      ReportTypeParamSetToNoType(param.name, param.loc, diag_);
  }

  DiagEngine& diag_;
};

}  // namespace

void ReportTypeParametersSetToNoTypes(const CompilationUnit& unit,
                                      DiagEngine& diag) {
  TypeParameterValueWalk(unit, diag).WalkUnit(unit);
}

}  // namespace delta
