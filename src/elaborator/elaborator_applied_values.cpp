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

// The value a member access a procedure writes is applied to, as far as the
// scope elaborator_call_targets.cpp walks the procedure in tells it, and the
// report of a member no value of its kind has: a string's or an enumeration's
// name that is none of its type's built-in methods (§6.16, §6.19.5), and any
// name applied to an integral or real value (§23.7).

namespace delta {

namespace {

// §6.18 with §26.3: the type the type `type`, written among the items of the
// scope, stands for, through each typedef it is written as (ThroughTypedefsAt).
SitedType ThroughTypedefs(const DataScope& scope, const DataType& type) {
  return ThroughTypedefsAt(scope.unit, {&type, scope.Site()});
}

// §6.18 with §23.9: the type the type the variable `var` is declared with
// stands for, its typedefs looked up from the scope declaring it.
SitedType VarType(const DataScope& scope, const DeclaredVar& var) {
  return ThroughTypedefsAt(scope.unit, {var.type, scope.SiteOf(var)});
}

// §6.19.5: the built-in methods of an enumeration.
constexpr std::string_view kEnumMethods[] = {"first", "last", "next",
                                             "prev",  "num",  "name"};

// §8.13: the member of kind `kind` named `name` the class `cls` or the nearest
// class it extends declares; null where none does. Each base is looked up from
// the scope's site; no class is its own ancestor (§8.13), so the walk ends.
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

// §6.18: the kind of the type `type` stands for, through the typedefs the
// scope sees it written as, where it is a single value; kImplicit where those
// typedefs make it an array (§7.4).
DataTypeKind ScalarKind(const DataScope& scope, const DataType& type) {
  const SitedType kNamed = ThroughTypedefs(scope, type);
  return kNamed.dims == 0 ? kNamed.type->kind : DataTypeKind::kImplicit;
}

// §8.13: the type `written`, a method's return type (§13.4.1) or a property's
// type (§8.5) the class `cls` declares, stands for: a name, written without a
// scope, that the class or a class it extends declares as a type is its
// typedef there, whose unpacked dimensions are added to `dims`, and any other
// type is itself, as the scope sees it; null where the class's name is a type
// parameter or a nested class.
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

// The kind of that type as a single value; kImplicit where it is none, or its
// class's typedef writes unpacked dimensions.
DataTypeKind ClassTypeKind(const DataType& written, const ClassDecl& cls,
                           const DataScope& scope) {
  std::size_t dims = 0;
  const DataType* type = ClassLocalType(written, cls, scope, dims);
  return type == nullptr || dims != 0 ? DataTypeKind::kImplicit
                                      : ScalarKind(scope, *type);
}

// §G.1: the class of the std package whose handle `e` holds, where the scope
// tells it for certain: a variable of the scope declared as one, process p,
// where no class of the design takes the name, or a call of a method of one
// returning one, process::self() or p.self(); none for anything else.
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

// §G.3 to §G.7: the kind of type the method `method` of the std class `owner`
// returns: an int, num()'s and the try_ methods' (§15.3, §15.4), a string,
// get_randstate()'s, or process's enumeration state, status()'s (§9.7);
// kImplicit for any other.
DataTypeKind StdResultKind(StdPackageMember owner, std::string_view method) {
  const StdMethodPrototype* prototype = StdMethodNamed(owner, method);
  const std::string_view kReturns =
      prototype == nullptr ? std::string_view() : prototype->return_type;
  if (kReturns == "int") return DataTypeKind::kInt;
  if (kReturns == "string") return DataTypeKind::kString;
  return kReturns == "state" ? DataTypeKind::kEnum : DataTypeKind::kImplicit;
}

// §13.4.1 with §23.9: the kind of type the call of `name`, written alone,
// returns: in a method of a class, a method the class or a class it extends
// declares (§8.13), else a function the items of the scope declare; kImplicit
// where neither does.
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

// §13.4.1: the kind of type the call whose callee is `callee` returns as a
// single value, where the scope tells it for certain: a function or method
// called by its name alone, f(); a method of a std class (§G.3 to §G.7),
// p.status(); a method of the class a handle holds, h.get(); and one of the
// methods every class has built in, randomize(), which returns an int
// (§18.6.1), and get_randstate(), which returns a string (§18.13.4), the rest
// being void; kImplicit for any other call.
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

// §20, §21 and §16.9: the kind of the value the system function `name`
// returns, or of the element `selects` selects of it reach (A.8.4): a string,
// whose element is a byte, for $sformatf (§21.3.3) and $typename (§20.6.1);
// none told for one returning its argument's type, $sampled and $past
// (§16.9.3) and the global clocking $past_gclk and $future_gclk (§16.9.4);
// and an integral or real value for every other, one an application defines
// through the VPI among them (§38.36).
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

// The value a member access is applied to, as far as the scope tells it: the
// kind of its type, how a report names it, and whether it is a property of
// the class whose method writes it, which may be random (§18.8).
struct AppliedValue {
  DataTypeKind kind = DataTypeKind::kImplicit;
  std::string named;
  bool property = false;
};

// §8.5: the value the property `root` names of the class a handle holds, h.x,
// written `selects` selects in front of a member access: of the property's
// type where the selects reach an element of each unpacked dimension it
// writes (§7.4); untyped where the scope tells no class the handle holds, or
// that class declares no such property.
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

// The value `root`, written `selects` selects in front of a member access,
// stands for: a variable of the scope or an element of one, one select per
// unpacked dimension its declaration and its typedefs write (§6.18, §7.4), the
// result of a call (§13.4.1) or of a system function, or a property of the
// class a handle holds.
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
