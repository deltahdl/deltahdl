#include <algorithm>
#include <cstdint>
#include <functional>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_class_typedef_specialization.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_operations.h"
#include "elaborator/expression_self_type.h"
#include "elaborator/net_data_type.h"
#include "elaborator/net_or_variable_type.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_enum_member.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/type_eval.h"
#include "elaborator/unpacked_array_type.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

// §6.23: the data type each operand of a comparison of two type references
// stands for, which the comparison folds by (§6.22.1): a type as written, a
// name a typedef or a scope's typedef gives, or the self-determined type of an
// expression.

namespace delta {

// §6.23 with §26.3, §8.23 and §6.25: the type a scope-qualified name in a type
// reference stands for. A typedef of a parameterized class is specialized,
// with arguments folded outside any module's scope; a package's or class's
// typedef is read under its "scope::name" key, or from a class the key misses,
// one declared inside a module. Nothing where the name resolves to none, or to
// a type carrying unpacked dimensions, which a data type alone does not hold.
static std::optional<DataType> ScopedTypeRefType(const DataType& dt,
                                                 const TypedefMap& typedefs,
                                                 const CompilationUnit* unit,
                                                 Arena& arena) {
  if (auto spec = SpecializeClassScopedType(dt, unit, {}, typedefs, arena)) {
    if (!spec->unpacked_dims.empty()) return std::nullopt;
    return spec->type;
  }
  auto it = typedefs.find(std::string(dt.scope_name) +
                          "::" + std::string(dt.type_name));
  if (it != typedefs.end()) return it->second;
  const DataType* in_class =
      FindClassScopedTypedefType(dt.scope_name, dt.type_name, unit);
  if (in_class != nullptr) return *in_class;
  return std::nullopt;
}

// Whether `e` is a scope resolution of one identifier by another, `p::t_s`.
static bool IsScopedTypeName(const Expr* e) {
  return e != nullptr && e->kind == ExprKind::kMemberAccess &&
         e->is_scope_resolution && e->lhs != nullptr &&
         e->lhs->kind == ExprKind::kIdentifier && e->rhs != nullptr &&
         e->rhs->kind == ExprKind::kIdentifier;
}

// The data type a type reference names as written, before any name in it is
// resolved: the one the parser read, or a name standing alone or behind a
// package's scope. Nothing for a type reference to an expression.
static std::optional<DataType> TypeRefWrittenType(const Expr* op) {
  if (op->type_value != nullptr) {
    // The data type the parser read, packed dimensions and signing included:
    // `type(bit[12:0])` is a 13-bit vector, where its name alone is `bit`.
    return *op->type_value;
  }
  if (!op->text.empty()) return TypeNameToDataType(op->text);
  if (op->lhs && op->lhs->kind == ExprKind::kIdentifier)
    return TypeNameToDataType(op->lhs->text);
  if (!IsScopedTypeName(op->lhs)) return std::nullopt;
  // `type(p::t_s)` with p a package reads as a scope resolution expression.
  DataType dt;
  dt.kind = DataTypeKind::kNamed;
  dt.scope_name = op->lhs->lhs->text;
  dt.type_name = op->lhs->rhs->text;
  return dt;
}

// Whether the type a type reference writes is a name alone, which may name a
// value rather than a type.
static bool IsBareName(const DataType& dt) {
  return dt.kind == DataTypeKind::kNamed && dt.scope_name.empty() &&
         dt.packed_dim_left == nullptr && dt.extra_packed_dims.empty();
}

// The type `dt` stands for once each name it is written by is read through:
// a built-in type keyword, a typedef, or a package's or class's typedef behind
// its scope. Nothing where a name resolves to none of them.
static std::optional<DataType> ThroughTypeNames(DataType dt,
                                                const TypedefMap& typedefs,
                                                const CompilationUnit* unit,
                                                Arena& arena) {
  for (int depth = 0; depth < 16 && dt.kind == DataTypeKind::kNamed; ++depth) {
    if (!dt.scope_name.empty()) {
      auto scoped = ScopedTypeRefType(dt, typedefs, unit, arena);
      if (!scoped) break;
      dt = *scoped;
      continue;
    }
    DataType builtin = TypeNameToDataType(dt.type_name);
    if (builtin.kind != DataTypeKind::kNamed) return builtin;
    auto it = typedefs.find(dt.type_name);
    if (it == typedefs.end()) break;
    dt = it->second;
  }
  if (dt.kind == DataTypeKind::kNamed) return std::nullopt;
  return dt;
}

// The function, or the imported DPI function (§35.5.4), named `name` among
// `items`; an out-of-block class method (§8.24) is its class's.
static const ModuleItem* FunctionAmong(const std::vector<ModuleItem*>& items,
                                       std::string_view name) {
  auto it = std::ranges::find_if(items, [&](const ModuleItem* item) {
    if (item == nullptr || item->name != name) return false;
    if (item->kind == ModuleItemKind::kDpiImport) return !item->dpi_is_task;
    return item->kind == ModuleItemKind::kFunctionDecl &&
           item->method_class.empty();
  });
  return it != items.end() ? *it : nullptr;
}

// §26.3: the package `scoped`, a `p::f` scope resolution, names, and the
// function or imported DPI function it declares by the name after it.
static const ModuleItem* PackageFunction(const Expr* scoped,
                                         const CompilationUnit* unit) {
  if (unit == nullptr || scoped == nullptr ||
      scoped->kind != ExprKind::kMemberAccess || !scoped->is_scope_resolution ||
      scoped->lhs == nullptr || scoped->lhs->kind != ExprKind::kIdentifier ||
      scoped->rhs == nullptr || scoped->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  auto pkg = std::ranges::find_if(unit->packages, [&](const PackageDecl* p) {
    return p != nullptr && p->name == scoped->lhs->text;
  });
  if (pkg == unit->packages.end()) return nullptr;
  return FunctionAmong((*pkg)->items, scoped->rhs->text);
}

// §13.4.1 with §26.3, §3.12.1 and §35.5.4: the function a call by a bare name
// reaches: one the module declares or imports from a package, then an
// imported DPI function the module declares, then a function or imported DPI
// function of the compilation unit.
const ModuleItem* ElaboratorOperationRules::BareNamedFunction(
    std::string_view name) const {
  auto it = func_decls_.find(name);
  if (it != func_decls_.end()) return it->second;
  if (!module_decl_path_.empty() && module_decl_path_.back() != nullptr) {
    if (const ModuleItem* fn =
            FunctionAmong(module_decl_path_.back()->items, name))
      return fn;
  }
  return unit_ != nullptr ? FunctionAmong(unit_->cu_items, name) : nullptr;
}

std::optional<DataType> ElaboratorOperationRules::CalledFunctionType(
    const Expr* e) const {
  if (e == nullptr || e->kind != ExprKind::kCall) return std::nullopt;
  if (const ModuleItem* fn = RegisteredConstFunc(e)) return fn->return_type;
  const ModuleItem* fn = nullptr;
  if (e->lhs == nullptr || e->lhs->kind == ExprKind::kIdentifier) {
    fn = BareNamedFunction(e->callee);
  } else {
    fn = PackageFunction(e->lhs, unit_);
  }
  if (fn == nullptr) return ClassScopedCallType(e->lhs);
  return fn->return_type;
}

// The arguments a class's unadorned name is written with: none, which makes
// it the default specialization (§8.25).
static const std::vector<DataType>& NoArguments() {
  static const std::vector<DataType> kNone;
  return kNone;
}

// §8.10 with §8.23: a static method called through the class scope operator,
// `C::f()`, `p::C::f()` or `Outer::Inner::f()`, gives its return type.
std::optional<DataType> ElaboratorOperationRules::ClassScopedCallType(
    const Expr* scoped) const {
  if (unit_ == nullptr || scoped == nullptr ||
      scoped->kind != ExprKind::kMemberAccess || !scoped->is_scope_resolution ||
      scoped->rhs == nullptr) {
    return std::nullopt;
  }
  std::vector<const ClassDecl*> chain =
      ClassChainOfScopePrefix(scoped->lhs, unit_);
  if (chain.empty()) return std::nullopt;
  std::optional<UnpackedArrayType> method = MemberTypeOf(
      {chain.back(), &NoArguments()}, scoped->rhs->text, gen_const_scope_);
  if (!method || !method->dims.empty()) return std::nullopt;
  return std::move(method->element);
}

std::optional<ClassSpecialization> ElaboratorOperationRules::ClassTypeOf(
    const DataType& type) const {
  if (unit_ == nullptr) return std::nullopt;
  const DataType* at = &type;
  for (int names = 0; names < 16 && at->kind == DataTypeKind::kNamed; ++names) {
    if (!at->scope_name.empty() || class_names_.contains(at->type_name)) {
      const ClassDecl* cls = ClassOfDeclaredType(*at, {}, unit_);
      if (cls == nullptr) return std::nullopt;
      return ClassSpecialization{cls, &at->type_params};
    }
    auto named = typedefs_.find(at->type_name);
    if (named == typedefs_.end()) return std::nullopt;
    at = &named->second;
  }
  return std::nullopt;
}

std::optional<UnpackedArrayType> ElaboratorOperationRules::MemberTypeOf(
    const ClassSpecialization& handle, std::string_view name,
    const ScopeMap& constants) const {
  OwnedMember owned = FindMemberAndOwner(handle.cls, name, unit_);
  if (owned.member == nullptr) return std::nullopt;
  const ClassMember& member = *owned.member;
  SpecializedClassType written;
  if (member.kind == ClassMemberKind::kProperty) {
    written = {member.data_type, member.unpacked_dims};
  } else if (member.kind == ClassMemberKind::kMethod &&
             member.method != nullptr &&
             member.method->kind == ModuleItemKind::kFunctionDecl) {
    written = {member.method->return_type, {}};
  } else {
    return std::nullopt;
  }
  // §8.13: a member the class inherits is read in the class declaring it,
  // whose own parameters the handle's specialization does not give.
  if (owned.owner != handle.cls && !owned.owner->params.empty())
    return std::nullopt;
  const ClassSpecialization kOwner{
      owned.owner, owned.owner == handle.cls ? handle.args : &NoArguments()};
  std::optional<SpecializedClassType> typed =
      SpecializedMemberType(kOwner, written, constants, typedefs_, arena_);
  if (!typed) return std::nullopt;
  return UnpackedArrayType{std::move(typed->type),
                           std::move(typed->unpacked_dims)};
}

std::optional<UnpackedArrayType> ElaboratorOperationRules::ClassMemberType(
    const DataType& handle, std::string_view name,
    const ScopeMap& constants) const {
  std::optional<ClassSpecialization> cls = ClassTypeOf(handle);
  if (!cls) return std::nullopt;
  return MemberTypeOf(*cls, name, constants);
}

std::optional<bool> ElaboratorOperationRules::DataTypesMatch(
    const DataType& a, const DataType& b, const ScopeMap& constants) const {
  std::optional<ClassSpecialization> class_a = ClassTypeOf(a);
  std::optional<ClassSpecialization> class_b = ClassTypeOf(b);
  if (class_a && class_b)
    return SameSpecialization(*class_a, *class_b, constants, typedefs_);
  if (class_a || class_b) {
    // §6.22.1(d): a class matches no type but a class.
    if (!ThroughTypeNames(class_a ? b : a, typedefs_, unit_, arena_))
      return std::nullopt;
    return false;
  }
  std::optional<DataType> type_a =
      ThroughTypeNames(a, typedefs_, unit_, arena_);
  std::optional<DataType> type_b =
      ThroughTypeNames(b, typedefs_, unit_, arena_);
  if (!type_a || !type_b) return std::nullopt;
  return TypesMatch(*type_a, *type_b);
}

std::optional<UnpackedArrayType> ElaboratorOperationRules::TypeRefOperandArray(
    const Expr* op, const RtlirModule* mod) const {
  std::optional<DataType> written = TypeRefWrittenType(op);
  // §6.23: a name the module declares a value by -- a net or variable, then a
  // parameter or an enumeration's named constant -- is an expression,
  // standing for the value's type, which a typedef or nettype names in turn.
  if (written && mod != nullptr && IsBareName(*written)) {
    std::optional<UnpackedArrayType> value;
    InExprTypeScope(*mod, [&](const ExprTypeScope& scope) {
      if (std::optional<DeclaredValue> declared =
              scope.value_named(written->type_name)) {
        value = ValueArrayType(*declared);
      }
    });
    if (value) return value;
  }
  if (written) return UnpackedArrayType{std::move(*written), {}};
  if (std::optional<DataType> returned = CalledFunctionType(op->lhs))
    return UnpackedArrayType{std::move(*returned), {}};
  return TypeRefArrayType(op->lhs, mod);
}

TypeShapeTables ElaboratorOperationRules::ArrayTables() const {
  return TypeShapeTables{typedefs_, td_array_dims_, class_names_};
}

std::optional<UnpackedArrayType>
ElaboratorOperationRules::ResolveTypeRefOperandArray(
    const Expr* op, const RtlirModule* mod) const {
  if (!op || op->kind != ExprKind::kTypeRef) return std::nullopt;
  std::optional<UnpackedArrayType> written = TypeRefOperandArray(op, mod);
  if (!written) return std::nullopt;
  UnpackedArrayType array = WithTypedefDims(
      written->element, std::move(written->dims), ArrayTables());
  // §8.4: a class is a type of its own, which DataTypesMatch matches by the
  // class and its specialization.
  if (ClassTypeOf(array.element)) return array;
  std::optional<DataType> element =
      ThroughTypeNames(array.element, typedefs_, unit_, arena_);
  if (!element) return std::nullopt;
  array.element = std::move(*element);
  return array;
}

std::optional<DataType> ElaboratorOperationRules::ResolveTypeRefOperandType(
    const Expr* op, const RtlirModule* mod) const {
  std::optional<UnpackedArrayType> array = ResolveTypeRefOperandArray(op, mod);
  if (!array || !array->dims.empty()) return std::nullopt;
  return std::move(array->element);
}

// §6.20.2: the type a value parameter stands for: the one it is declared
// with, or, declared with none, real for a real value and otherwise the logic
// vector of its range or of its final value.
static DataType ParamValueType(const RtlirParamDecl& param, Arena& arena) {
  if (param.decl_type != nullptr && !param.decl_type_implicit) {
    return *param.decl_type;
  }
  if (param.is_real_value) return TypeNameToDataType("real");
  ParamStorageShape shape = ParamStorageShapeOf(param);
  return VectorType(shape.width, shape.is_signed, true, arena);
}

// §6.19.3: the type of an enumeration's named constant `name` that `mod`
// declares: the typedef naming the enumeration, or the enumeration as written
// where no typedef names it.
static std::optional<DataType> EnumConstantType(const RtlirModule& mod,
                                                std::string_view name,
                                                const TypedefMap& typedefs) {
  for (const auto& [key, members] : mod.enum_types) {
    auto constant = std::ranges::find(members, name, &RtlirEnumMember::name);
    if (constant == members.end()) continue;
    if (typedefs.contains(key)) return TypeNameToDataType(key);
    if (constant->enumeration != nullptr) return *constant->enumeration;
  }
  return std::nullopt;
}

// Where a name an expression in a type reference writes is looked up: the
// module, the generate blocks in force at the reference with the names their
// declarations are recorded under, the typedefs, and the arena a parameter's
// vector type is made in.
namespace {
struct ValueLookup {
  const RtlirModule& mod;
  ScopedDeclarations declarations;
  const TypedefMap& typedefs;
  Arena& arena;
};
}  // namespace

// The value `name` stands for: a net, variable or port, then a value
// parameter the generate blocks in force see, then an enumeration's named
// constant.
static std::optional<DeclaredValue> ValueIn(std::string_view name,
                                            const ValueLookup& lookup) {
  const ScopedDeclarations& declarations = lookup.declarations;
  std::string_view declared =
      DeclaredScopedName(name, declarations.scopes, declarations.declared);
  if (std::optional<DeclaredValue> value =
          NetOrVariableValue(lookup.mod, declared)) {
    return value;
  }
  auto param =
      std::ranges::find_if(lookup.mod.params, [&](const RtlirParamDecl& p) {
        return p.name == name && !p.is_type_param &&
               ParamVisibleFromScopes(p.gen_block_prefix, declarations.scopes);
      });
  if (param != lookup.mod.params.end()) {
    // §7.4: a parameter may be an unpacked array, of fixed size.
    DeclaredValue value{ParamValueType(*param, lookup.arena)};
    if (param->unpacked_dims != nullptr) {
      value.dims = *param->unpacked_dims;
      value.unpacked_dims = static_cast<uint32_t>(value.dims.size());
    }
    return value;
  }
  if (std::optional<DataType> type =
          EnumConstantType(lookup.mod, name, lookup.typedefs)) {
    return DeclaredValue{*type};
  }
  return std::nullopt;
}

// §11.2.1: the constants of `mod` an expression in a type reference may fold
// a bound or a size against: the generate constants in force, `generate`,
// over the module's resolved value parameters and its enumerations' named
// constants.
static ScopeMap ConstantsIn(const RtlirModule& mod, const ScopeMap& generate) {
  ScopeMap constants = generate;
  for (const RtlirParamDecl& param : mod.params) {
    if (param.is_resolved && !param.is_type_param && !param.is_real_value) {
      constants.try_emplace(param.name, param.resolved_value);
    }
  }
  for (const auto& enumeration : mod.enum_types) {
    for (const RtlirEnumMember& constant : enumeration.second) {
      constants.try_emplace(constant.name, constant.value);
    }
  }
  return constants;
}

void ElaboratorOperationRules::InExprTypeScope(
    const RtlirModule& mod,
    const std::function<void(const ExprTypeScope&)>& use) const {
  ScopeMap constants = ConstantsIn(mod, gen_const_scope_);
  ValueLookup lookup{
      mod, {gen_prefix_scopes_, declared_names_}, typedefs_, arena_};
  const TypeShapeTables kTables = ArrayTables();
  ExprTypeScope scope{
      [&](std::string_view name) { return ValueIn(name, lookup); },
      [this](const Expr* call) { return CalledFunctionType(call); },
      [&](const Expr* ref) { return ResolveTypeRefOperandType(ref, &mod); },
      typedefs_,
      constants,
      arena_};
  scope.array_tables = &kTables;
  scope.class_member = [this, &constants](const DataType& handle,
                                          std::string_view name) {
    return ClassMemberType(handle, name, constants);
  };
  use(scope);
}

std::optional<DataType> ElaboratorOperationRules::TypeRefExprType(
    const Expr* expr, const RtlirModule* mod) const {
  if (expr == nullptr || mod == nullptr) return std::nullopt;
  std::optional<DataType> type;
  InExprTypeScope(*mod, [&](const ExprTypeScope& scope) {
    type = ExprSelfType(expr, scope);
  });
  return type;
}

std::optional<UnpackedArrayType> ElaboratorOperationRules::TypeRefArrayType(
    const Expr* expr, const RtlirModule* mod) const {
  if (expr == nullptr || mod == nullptr) return std::nullopt;
  std::optional<UnpackedArrayType> array;
  InExprTypeScope(*mod, [&](const ExprTypeScope& scope) {
    array = ExprSelfArrayType(expr, scope);
  });
  return array;
}

std::optional<UnpackedArrayType> ElaboratorOperationRules::TypeRefValueArray(
    const Expr* ref, const RtlirModule* mod) const {
  std::optional<UnpackedArrayType> array = TypeRefArrayType(ref, mod);
  if (!array) return std::nullopt;
  UnpackedArrayType whole =
      WithTypedefDims(array->element, std::move(array->dims), ArrayTables());
  if (whole.dims.empty()) return std::nullopt;
  return whole;
}

std::vector<Expr*> ElaboratorOperationRules::TypeRefUnpackedDims(
    const Expr* ref, const RtlirModule* mod) const {
  std::optional<UnpackedArrayType> array = TypeRefValueArray(ref, mod);
  if (!array) return {};
  return std::move(array->dims);
}

// §6.23 — a comparison of two type references is a constant expression whose
// result is true exactly when the referenced types match per §6.22.1 (equality
// forms yield that truth value; inequality forms its negation). Fold such a
// comparison to 0/1 so it can drive an elaboration-time selection (e.g. a
// generate-if). Returns nullopt when this is not a two-type-reference
// comparison or either operand's type cannot be resolved.
std::optional<bool> ElaboratorOperationRules::TypeRefsMatch(
    const Expr* a, const Expr* b, const RtlirModule* mod) const {
  std::optional<UnpackedArrayType> type_a = ResolveTypeRefOperandArray(a, mod);
  std::optional<UnpackedArrayType> type_b = ResolveTypeRefOperandArray(b, mod);
  if (!type_a || !type_b) return std::nullopt;
  // §7.4.2 and §8.25: a fixed-size dimension's bounds and a specialization's
  // values fold against the module's constants and the generate constants in
  // force.
  const ScopeMap kConstants =
      mod != nullptr ? ConstantsIn(*mod, gen_const_scope_) : gen_const_scope_;
  return UnpackedArrayTypesMatch(*type_a, *type_b, ArrayTables(), kConstants,
                                 [&](const DataType& x, const DataType& y) {
                                   return DataTypesMatch(x, y, kConstants);
                                 });
}

std::optional<int64_t> ElaboratorOperationRules::EvalConstTypeRefCompare(
    const Expr* expr, const RtlirModule* mod) const {
  if (!IsTypeRefComparison(expr)) return std::nullopt;
  std::optional<bool> matched = TypeRefsMatch(expr->lhs, expr->rhs, mod);
  if (!matched) return std::nullopt;
  bool is_negated =
      expr->op == TokenKind::kBangEq || expr->op == TokenKind::kBangEqEq;
  return (*matched != is_negated) ? 1 : 0;
}

}  // namespace delta
