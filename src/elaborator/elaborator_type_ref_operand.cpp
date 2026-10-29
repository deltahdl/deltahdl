#include <algorithm>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/elaborator_class_typedef_specialization.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_operations.h"
#include "elaborator/expression_self_type.h"
#include "elaborator/net_or_variable_type.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_enum_member.h"
#include "elaborator/rtlir_scopes.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
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

std::optional<DataType> ElaboratorOperationRules::CalledFunctionType(
    const Expr* e) const {
  if (e == nullptr || e->kind != ExprKind::kCall ||
      (e->lhs != nullptr && e->lhs->kind != ExprKind::kIdentifier))
    return std::nullopt;
  if (const ModuleItem* fn = RegisteredConstFunc(e)) return fn->return_type;
  auto it = func_decls_.find(e->callee);
  if (it == func_decls_.end()) return std::nullopt;
  return it->second->return_type;
}

std::optional<DataType> ElaboratorOperationRules::ResolveTypeRefOperandType(
    const Expr* op, const RtlirModule* mod) const {
  if (!op || op->kind != ExprKind::kTypeRef) return std::nullopt;
  std::optional<DataType> written = TypeRefWrittenType(op);
  if (!written) written = CalledFunctionType(op->lhs);
  if (!written) written = TypeRefExprType(op->lhs, mod);
  if (!written) return std::nullopt;
  DataType dt = *written;
  // §6.23: a name the module declares a value by -- a net or variable, then a
  // parameter or an enumeration's named constant -- is an expression,
  // standing for the value's type, which a typedef or nettype names in turn.
  if (mod != nullptr && IsBareName(dt)) {
    std::string_view declared =
        DeclaredScopedName(dt.type_name, gen_prefix_scopes_, declared_names_);
    std::optional<DataType> value = NetOrVariableType(*mod, declared);
    if (!value) value = TypeRefExprType(op->lhs, mod);
    if (value) dt = *value;
  }
  return ThroughTypeNames(dt, typedefs_, unit_, arena_);
}

// §6.23 — a comparison of two type references is a constant expression whose
// result is true exactly when the referenced types match per §6.22.1 (equality
// forms yield that truth value; inequality forms its negation). Fold such a
// comparison to 0/1 so it can drive an elaboration-time selection (e.g. a
// generate-if). Returns nullopt when this is not a two-type-reference
// comparison or either operand's type cannot be resolved.
std::optional<int64_t> ElaboratorOperationRules::EvalConstTypeRefCompare(
    const Expr* expr, const RtlirModule* mod) const {
  if (!IsTypeRefComparison(expr)) return std::nullopt;
  auto lhs_type = ResolveTypeRefOperandType(expr->lhs, mod);
  auto rhs_type = ResolveTypeRefOperandType(expr->rhs, mod);
  if (!lhs_type || !rhs_type) return std::nullopt;
  bool matched = TypesMatch(*lhs_type, *rhs_type);
  bool is_negated =
      expr->op == TokenKind::kBangEq || expr->op == TokenKind::kBangEqEq;
  return (matched != is_negated) ? 1 : 0;
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
    return DeclaredValue{ParamValueType(*param, lookup.arena)};
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

std::optional<DataType> ElaboratorOperationRules::TypeRefExprType(
    const Expr* expr, const RtlirModule* mod) const {
  if (expr == nullptr || mod == nullptr) return std::nullopt;
  ScopeMap constants = ConstantsIn(*mod, gen_const_scope_);
  ValueLookup lookup{
      *mod, {gen_prefix_scopes_, declared_names_}, typedefs_, arena_};
  ExprTypeScope scope{
      [&](std::string_view name) { return ValueIn(name, lookup); },
      [this](const Expr* call) { return CalledFunctionType(call); },
      [&](const Expr* ref) { return ResolveTypeRefOperandType(ref, mod); },
      typedefs_,
      constants,
      arena_};
  return ExprSelfType(expr, scope);
}

}  // namespace delta
