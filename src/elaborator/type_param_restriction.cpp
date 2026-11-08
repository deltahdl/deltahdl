#include "elaborator/type_param_restriction.h"

#include <cstddef>
#include <format>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

const DataType* ResolveNamedTypeChain(const DataType* dtype,
                                      const TypedefMap& typedefs) {
  for (int hops = 0; hops < 8 && dtype->kind == DataTypeKind::kNamed; ++hops) {
    auto td = typedefs.find(dtype->type_name);
    if (td == typedefs.end()) break;
    dtype = &td->second;
  }
  return dtype;
}

void ReportNotOfClassKind(const RestrictedTypeParam& param,
                          const DataType& resolved, SourceLoc loc,
                          const TypeParamRestrictionScope& scope,
                          DiagEngine& diag) {
  const bool kWantsInterface = param.restriction == DataTypeKind::kVoid;
  const std::string_view kRestriction =
      kWantsInterface ? "an interface class" : "a class";
  if (resolved.kind != DataTypeKind::kNamed) {
    diag.ErrorOnce(loc,
                   std::format("type parameter '{}' is restricted to {} type "
                               "but is assigned a type that is not a class",
                               param.name, kRestriction),
                   Subclause("6.20.3"));
    return;
  }
  const ClassDecl* cls = FindClassDecl(resolved.type_name, scope.unit);
  const bool kIsKnownClass =
      cls != nullptr || scope.class_names.count(resolved.type_name) > 0;
  if (!kIsKnownClass) {
    diag.ErrorOnce(loc,
                   std::format("type parameter '{}' is restricted to {} type "
                               "but is assigned '{}', which no class "
                               "declaration defines",
                               param.name, kRestriction, resolved.type_name),
                   Subclause("6.20.3"));
    return;
  }
  const bool kIsInterface = cls != nullptr && cls->is_interface;
  if (kIsInterface == kWantsInterface) return;
  diag.ErrorOnce(
      loc,
      std::format("type parameter '{}' is restricted to {} type but is "
                  "assigned '{}', which is {}",
                  param.name, kRestriction, resolved.type_name,
                  kIsInterface ? "an interface class" : "an ordinary class"),
      Subclause("6.20.3"));
}

std::string_view AggregateKindName(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kEnum:
      return "enum";
    case DataTypeKind::kStruct:
      return "struct";
    default:
      return "union";
  }
}

void ReportNotOfAggregateKind(const RestrictedTypeParam& param,
                              const DataType& resolved, SourceLoc loc,
                              DiagEngine& diag) {
  if (resolved.kind == DataTypeKind::kNamed ||
      resolved.kind == param.restriction)
    return;
  diag.ErrorOnce(loc,
                 std::format("type parameter '{}' is assigned a type that "
                             "does not conform to the required {} kind",
                             param.name, AggregateKindName(param.restriction)),
                 Subclause("6.20.3"));
}

void ReportClassHeaderDefaults(const ClassDecl& cls,
                               const TypeParamRestrictionScope& scope,
                               DiagEngine& diag) {
  for (std::size_t i = 0; i < cls.params.size(); ++i) {
    auto restriction = cls.type_param_restrictions.find(cls.params[i].first);
    if (restriction == cls.type_param_restrictions.end()) continue;
    ReportTypeOutsideRestriction({restriction->first, restriction->second},
                                 cls.param_types.at(i),
                                 cls.param_port_locs.at(i), scope, diag);
  }
}

void ReportClassBodyDefaults(const ClassDecl& cls,
                             const TypeParamRestrictionScope& scope,
                             DiagEngine& diag) {
  for (const ClassMember* m : cls.members) {
    if (m->type_param_restriction == DataTypeKind::kImplicit) continue;
    ReportTypeOutsideRestriction({m->name, m->type_param_restriction},
                                 m->typedef_item->typedef_type,
                                 m->typedef_item->loc, scope, diag);
  }
}

}  // namespace

void ReportTypeOutsideRestriction(const RestrictedTypeParam& param,
                                  const DataType& assigned, SourceLoc loc,
                                  const TypeParamRestrictionScope& scope,
                                  DiagEngine& diag) {
  if (assigned.kind == DataTypeKind::kImplicit) return;
  const DataType* resolved = ResolveNamedTypeChain(&assigned, scope.typedefs);
  switch (param.restriction) {
    case DataTypeKind::kEnum:
    case DataTypeKind::kStruct:
    case DataTypeKind::kUnion:
      ReportNotOfAggregateKind(param, *resolved, loc, diag);
      return;
    case DataTypeKind::kNamed:
    case DataTypeKind::kVoid:
      ReportNotOfClassKind(param, *resolved, loc, scope, diag);
      return;
    default:
      return;
  }
}

void ReportClassTypeParamsOutsideRestrictions(
    const TypeParamRestrictionScope& scope, DiagEngine& diag) {
  for (const ClassDecl* cls : AllClassDecls(scope.unit)) {
    ReportClassHeaderDefaults(*cls, scope, diag);
    ReportClassBodyDefaults(*cls, scope, diag);
  }
}

void ReportSpecializationOutsideRestrictions(
    const DataType& written, SourceLoc loc,
    const TypeParamRestrictionScope& scope, DiagEngine& diag) {
  const ClassDecl* cls = written.kind == DataTypeKind::kNamed
                             ? FindClassDecl(written.type_name, scope.unit)
                             : nullptr;
  if (cls == nullptr || written.type_params.empty()) return;
  for (std::size_t i = 0; i < cls->params.size(); ++i) {
    auto restriction = cls->type_param_restrictions.find(cls->params[i].first);
    if (restriction == cls->type_param_restrictions.end()) continue;
    const DataType* actual =
        SpecializationArgument(written.type_params, i, restriction->first);
    if (actual == nullptr) continue;
    ReportTypeOutsideRestriction({restriction->first, restriction->second},
                                 *actual, loc, scope, diag);
  }
}

}  // namespace delta
