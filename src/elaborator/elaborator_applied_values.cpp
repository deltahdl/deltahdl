#include <algorithm>
#include <cstddef>
#include <format>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/class_member_names.h"
#include "elaborator/elaborator_call_targets_internal.h"
#include "elaborator/std_package.h"
#include "elaborator/struct_member_selects.h"
#include "elaborator/type_eval.h"
#include "elaborator/type_site_lookup.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

SitedType ThroughTypedefs(const DataScope& scope, const DataType& type) {
  return ThroughTypedefsAt(scope.unit, {&type, scope.Site()});
}

SitedType VarType(const DataScope& scope, const DeclaredVar& var) {
  return ThroughTypedefsAt(scope.unit, {var.type, scope.SiteOf(var)});
}

constexpr std::string_view kEnumMethods[] = {"first", "last", "next",
                                             "prev",  "num",  "name"};

const ClassMember* ChainMember(const ClassDecl& cls, ClassMemberKind kind,
                               std::string_view name, const DataScope& scope) {
  const TypeSite kSite = scope.Site();
  for (const ClassDecl* walked = &cls; walked != nullptr;
       walked = BaseClassIn(scope.unit, kSite, *walked)) {
    for (const ClassMember* member : walked->members) {
      if (member->kind == kind && member->name == name) return member;
    }
  }
  return nullptr;
}

DataTypeKind ScalarKind(const DataScope& scope, const DataType& type) {
  const SitedType kNamed = ThroughTypedefs(scope, type);
  return kNamed.dims == 0 ? kNamed.type->kind : DataTypeKind::kImplicit;
}

const DataType* ClassLocalType(const DataType& written, const ClassDecl& cls,
                               const DataScope& scope, std::size_t& dims) {
  std::unordered_set<std::string_view> local;
  scope.classes->AddLocalTypes(cls, local);
  if (written.kind != DataTypeKind::kNamed || !written.scope_name.empty() ||
      !local.contains(written.type_name)) {
    return &written;
  }
  const ClassMember* def =
      ChainMember(cls, ClassMemberKind::kTypedef, written.type_name, scope);
  if (def == nullptr) return nullptr;
  dims += def->typedef_item->unpacked_dims.size();
  return &def->typedef_item->typedef_type;
}

DataTypeKind ClassTypeKind(const DataType& written, const ClassDecl& cls,
                           const DataScope& scope) {
  std::size_t dims = 0;
  const DataType* type = ClassLocalType(written, cls, scope, dims);
  return type == nullptr || dims != 0 ? DataTypeKind::kImplicit
                                      : ScalarKind(scope, *type);
}

std::optional<StdPackageMember> StdClassOf(const Expr& e,
                                           const DataScope& scope) {
  const Expr* callee = e.kind == ExprKind::kCall ? e.lhs : nullptr;
  if (callee != nullptr && callee->kind == ExprKind::kMemberAccess) {
    const std::optional<StdPackageMember> kOwner =
        callee->is_scope_resolution ? StdPackageMemberNamed(callee->lhs->text)
                                    : StdClassOf(*callee->lhs, scope);
    const StdMethodPrototype* prototype =
        kOwner ? StdMethodNamed(*kOwner, callee->rhs->text) : nullptr;
    return prototype == nullptr ? std::nullopt
                                : StdPackageMemberNamed(prototype->return_type);
  }
  const DeclaredVar* var =
      e.kind == ExprKind::kIdentifier ? scope.Declared(e.text) : nullptr;
  if (var == nullptr || var->type->kind != DataTypeKind::kNamed ||
      ClassNamed(scope, *var, 0) != nullptr) {
    return std::nullopt;
  }
  return StdPackageMemberNamed(var->type->type_name);
}

DataTypeKind StdResultKind(StdPackageMember owner, std::string_view method) {
  const StdMethodPrototype* prototype = StdMethodNamed(owner, method);
  const std::string_view kReturns =
      prototype == nullptr ? std::string_view() : prototype->return_type;
  if (kReturns == "int") return DataTypeKind::kInt;
  if (kReturns == "string") return DataTypeKind::kString;
  return kReturns == "state" ? DataTypeKind::kEnum : DataTypeKind::kImplicit;
}

DataTypeKind PlainCallKind(std::string_view name, const DataScope& scope) {
  const ClassMember* method =
      scope.cls == nullptr
          ? nullptr
          : ChainMember(*scope.cls, ClassMemberKind::kMethod, name, scope);
  if (method != nullptr) {
    return ClassTypeKind(method->method->return_type, *scope.cls, scope);
  }
  for (const ModuleItem* item : scope.items) {
    if (item->kind == ModuleItemKind::kFunctionDecl && item->name == name) {
      return ScalarKind(scope, item->return_type);
    }
  }
  return DataTypeKind::kImplicit;
}

DataTypeKind CallResultKind(const Expr& callee, const DataScope& scope) {
  if (callee.kind != ExprKind::kMemberAccess) {
    return PlainCallKind(callee.text, scope);
  }
  if (callee.is_scope_resolution) return DataTypeKind::kImplicit;
  const std::string_view kMethod = callee.rhs->text;
  if (const auto kStd = StdClassOf(*callee.lhs, scope)) {
    return StdResultKind(*kStd, kMethod);
  }
  const ClassDecl* cls = HandleClass(*callee.lhs, scope);
  if (cls == nullptr) return DataTypeKind::kImplicit;
  const ClassMember* method =
      ChainMember(*cls, ClassMemberKind::kMethod, kMethod, scope);
  if (method != nullptr) {
    return ClassTypeKind(method->method->return_type, *cls, scope);
  }
  if (kMethod == "randomize") return DataTypeKind::kInt;
  return kMethod == "get_randstate" ? DataTypeKind::kString
                                    : DataTypeKind::kImplicit;
}

DataTypeKind SystemCallKind(std::string_view name, std::size_t selects) {
  constexpr std::string_view kStrings[] = {"$sformatf", "$typename"};
  constexpr std::string_view kArgumentTyped[] = {"$sampled", "$past",
                                                 "$past_gclk", "$future_gclk"};
  if (std::ranges::count(kArgumentTyped, name) != 0) {
    return DataTypeKind::kImplicit;
  }
  const bool kString = selects == 0 && std::ranges::count(kStrings, name) != 0;
  return kString ? DataTypeKind::kString : DataTypeKind::kInt;
}

struct AppliedValue {
  DataTypeKind kind = DataTypeKind::kImplicit;
  std::string named;
  bool property = false;
};

AppliedValue HeldPropertyValue(const Expr& root, std::size_t selects,
                               const DataScope& scope) {
  AppliedValue value;
  const ClassDecl* cls = HandleClass(*root.lhs, scope);
  const ClassMember* property =
      cls == nullptr ? nullptr
                     : ChainMember(*cls, ClassMemberKind::kProperty,
                                   root.rhs->text, scope);
  if (property == nullptr) return value;
  if (property->unpacked_dims.size() == selects) {
    value.kind = ClassTypeKind(property->data_type, *cls, scope);
  }
  value.named = std::format("'{}'", root.rhs->text);
  value.property = true;
  return value;
}

AppliedValue ValueOf(const Expr& root, std::size_t selects,
                     const DataScope& scope) {
  AppliedValue value;
  const DeclaredVar* var =
      root.kind == ExprKind::kIdentifier ? scope.Declared(root.text) : nullptr;
  const Expr* callee =
      root.kind == ExprKind::kCall && selects == 0 ? root.lhs : nullptr;
  if (var != nullptr) {
    const SitedType kNamed = VarType(scope, *var);
    if (var->dims + kNamed.dims == selects) value.kind = kNamed.type->kind;
    value.named = std::format("'{}'", root.text);
    value.property = scope.Property(root.text) == var;
  } else if (callee != nullptr) {
    value.kind = CallResultKind(*callee, scope);
    const std::string_view kCalled = callee->kind == ExprKind::kMemberAccess
                                         ? callee->rhs->text
                                         : callee->text;
    value.named = std::format("that '{}()' returns", kCalled);
  } else if (root.kind == ExprKind::kSystemCall) {
    value.kind = SystemCallKind(root.callee, selects);
    value.named = std::format("that '{}' returns", root.callee);
  } else if (root.kind == ExprKind::kMemberAccess &&
             !root.is_scope_resolution) {
    value = HeldPropertyValue(root, selects, scope);
  }
  return value;
}

}  // namespace

const ClassDecl* ClassNamed(const DataScope& scope, const DeclaredVar& var,
                            std::size_t selects) {
  const auto [named, site, dims] = VarType(scope, var);
  if (var.dims + dims != selects) return nullptr;
  if (!named->scope_name.empty()) {
    return ScopedClass(scope.unit, site, named->scope_name, named->type_name);
  }
  return ClassIn(scope.unit, site, named->type_name);
}

const Expr& SelectRoot(const Expr& e, std::size_t& selects) {
  const Expr* root = &e;
  while (root->kind == ExprKind::kSelect && root->base != nullptr) {
    ++selects;
    root = root->base;
  }
  return *root;
}

const ClassDecl* HandleClass(const Expr& e, const DataScope& scope) {
  std::size_t selects = 0;
  const Expr& root = SelectRoot(e, selects);
  if (root.kind == ExprKind::kIdentifier) {
    const DeclaredVar* var = scope.Declared(root.text);
    const bool kClassType = var != nullptr &&
                            var->type->kind == DataTypeKind::kNamed &&
                            !scope.local_types.contains(var->type->type_name);
    return kClassType ? ClassNamed(scope, *var, selects) : nullptr;
  }
  if (root.kind != ExprKind::kMemberAccess) return nullptr;
  const ClassDecl* holder = HandleClass(*root.lhs, scope);
  return holder == nullptr
             ? nullptr
             : scope.classes->PropertyClass(*holder, root.rhs->text, selects);
}

SitedType HeldPropertyType(const Expr& access, const DataScope& scope) {
  const ClassDecl* cls = HandleClass(*access.lhs, scope);
  const ClassMember* property =
      cls == nullptr ? nullptr
                     : ChainMember(*cls, ClassMemberKind::kProperty,
                                   access.rhs->text, scope);
  if (property == nullptr) return {};
  std::size_t dims = property->unpacked_dims.size();
  const DataType* type = ClassLocalType(property->data_type, *cls, scope, dims);
  return type == nullptr ? SitedType{} : SitedType{type, scope.Site(), dims};
}

DataTypeKind AppliedValueKind(const Expr& value, const DataScope& scope) {
  return ValueOf(value, 0, scope).kind;
}

void ReportNoBuiltInMethod(const Expr& access, const DataScope& scope,
                           DiagEngine& diag) {
  std::size_t selects = 0;
  const Expr& root = SelectRoot(*access.lhs, selects);
  const AppliedValue kValue = ValueOf(root, selects, scope);
  const bool kString = kValue.kind == DataTypeKind::kString;
  const bool kEvent = kValue.kind == DataTypeKind::kEvent;
  const bool kBare = IsMemberlessKind(kValue.kind);
  if (!kString && !kEvent && !kBare && kValue.kind != DataTypeKind::kEnum) {
    return;
  }
  const std::string_view kName = access.rhs->text;
  const int kWhich = kString ? 0 : kEvent ? 1 : kBare ? 2 : 3;
  static constexpr std::string_view kEventMethods[] = {"triggered"};
  using Methods = std::span<const std::string_view>;
  const Methods kMethods[] = {kStringMethods, kEventMethods, Methods(),
                              kEnumMethods};
  if (std::ranges::find(kMethods[kWhich], kName) != kMethods[kWhich].end() ||
      (kWhich > 1 && kName == "rand_mode" && kValue.property))
    return;
  constexpr const char* kNouns[] = {"string", "event", "integral or real value",
                                    "enumeration"};
  constexpr const char* kRules[] = {"6.16", "15.5.3", "23.7", "6.19.5"};
  diag.Error(access.rhs->range.start,
             std::format("'{}' is not a built-in method of the {} {}", kName,
                         kNouns[kWhich], kValue.named),
             Subclause(kRules[kWhich]));
}

}  // namespace delta
