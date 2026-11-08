#include "elaborator/value_kind.h"

#include <algorithm>
#include <array>
#include <cstddef>
#include <span>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/aggregate_shape.h"
#include "elaborator/elaborator_data.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/net_data_type.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

constexpr std::array kArithmeticOps = {TokenKind::kPlus,    TokenKind::kMinus,
                                       TokenKind::kStar,    TokenKind::kSlash,
                                       TokenKind::kPercent, TokenKind::kPower};

using KindByName = std::pair<std::string_view, ValueKind>;

constexpr std::array<KindByName, 14> kStringMethods = {
    {{"len", ValueKind::kIntegral},
     {"getc", ValueKind::kIntegral},
     {"toupper", ValueKind::kString},
     {"tolower", ValueKind::kString},
     {"compare", ValueKind::kIntegral},
     {"icompare", ValueKind::kIntegral},
     {"substr", ValueKind::kString},
     {"atoi", ValueKind::kIntegral},
     {"atohex", ValueKind::kIntegral},
     {"atooct", ValueKind::kIntegral},
     {"atobin", ValueKind::kIntegral},
     {"atoreal", ValueKind::kReal},
     {"realtoa", ValueKind::kString},
     {"itoa", ValueKind::kString}}};

constexpr std::array<KindByName, 15> kCastKeywords = {
    {{"bit", ValueKind::kIntegral},
     {"logic", ValueKind::kIntegral},
     {"reg", ValueKind::kIntegral},
     {"byte", ValueKind::kIntegral},
     {"shortint", ValueKind::kIntegral},
     {"int", ValueKind::kIntegral},
     {"longint", ValueKind::kIntegral},
     {"integer", ValueKind::kIntegral},
     {"time", ValueKind::kIntegral},
     {"signed", ValueKind::kIntegral},
     {"unsigned", ValueKind::kIntegral},
     {"real", ValueKind::kReal},
     {"shortreal", ValueKind::kReal},
     {"realtime", ValueKind::kReal},
     {"string", ValueKind::kString}}};

ValueKind FindKind(std::span<const KindByName> table, std::string_view name) {
  auto it = std::ranges::find(table, name, &KindByName::first);
  return it != table.end() ? it->second : ValueKind::kUnknown;
}

}  // namespace

ValueKind KindOfTypeKind(DataTypeKind kind) {
  if (kind == DataTypeKind::kString) return ValueKind::kString;
  if (IsRealType(kind)) return ValueKind::kReal;
  if (IsIntegralType(kind) || IsNetTypeKind(kind)) return ValueKind::kIntegral;
  if (kind == DataTypeKind::kChandle || kind == DataTypeKind::kEvent) {
    return ValueKind::kOther;
  }
  return ValueKind::kUnknown;
}

namespace {

ValueKind KindOfTypeName(std::string_view name, const ValueScope& scope);

const DataType* Resolved(const DataType& type, const ValueScope& scope) {
  std::vector<std::string_view> names;
  return FollowTypedefs(type, scope.typedefs, names);
}

ValueKind KindOfType(const DataType& type, const ValueScope& scope) {
  const DataType* own = Resolved(type, scope);
  if (own == nullptr) return KindOfTypeName(type.type_name, scope);
  if (own->kind == DataTypeKind::kStruct || own->kind == DataTypeKind::kUnion) {
    return IsUnpackedAggregate(own) ? ValueKind::kOther : ValueKind::kIntegral;
  }
  return KindOfTypeKind(own->kind);
}

ValueKind KindOfTypeName(std::string_view name, const ValueScope& scope) {
  if (scope.class_names.count(name) != 0) return ValueKind::kOther;
  auto it = scope.typedefs.find(name);
  if (it == scope.typedefs.end()) return ValueKind::kUnknown;
  return KindOfType(it->second, scope);
}

bool IsIterator(std::string_view name, const ValueScope& scope) {
  return !name.empty() && name == scope.iterator.name;
}

ValueKind KindOfVariable(std::string_view name, const ValueScope& scope) {
  if (IsIterator(name, scope))
    return KindOfElement(*scope.iterator.array, scope);
  if (scope.arrays.count(name) != 0) return ValueKind::kOther;
  auto named = scope.var_named_types.find(name);
  if (named != scope.var_named_types.end()) {
    return KindOfTypeName(named->second, scope);
  }
  auto it = scope.var_types.find(name);
  return it != scope.var_types.end() ? KindOfTypeKind(it->second)
                                     : ValueKind::kUnknown;
}

const DataType* AggregateOf(const Expr* e, const ValueScope& scope);

const StructMember* MemberNamed(const DataType& aggregate,
                                std::string_view name) {
  auto it =
      std::ranges::find(aggregate.struct_members, name, &StructMember::name);
  return it != aggregate.struct_members.end() ? &*it : nullptr;
}

const StructMember* MemberOf(const Expr* e, const ValueScope& scope) {
  const DataType* outer = AggregateOf(e->lhs, scope);
  return outer != nullptr ? MemberNamed(*outer, e->rhs->text) : nullptr;
}

const DataType* DeclaredTypeOfName(std::string_view name,
                                   const ValueScope& scope) {
  if (IsIterator(name, scope)) return scope.iterator.array->elem_data_type;
  auto named = scope.var_named_types.find(name);
  if (named == scope.var_named_types.end()) return nullptr;
  auto td = scope.typedefs.find(named->second);
  return td != scope.typedefs.end() ? &td->second : nullptr;
}

const DataType* ElementDeclaredType(std::string_view name,
                                    const ValueScope& scope) {
  auto it = scope.arrays.find(name);
  return it != scope.arrays.end() && it->second.num_unpacked_dims == 1
             ? it->second.elem_data_type
             : nullptr;
}

const DataType* MemberDeclaredType(const Expr* e, const ValueScope& scope) {
  const StructMember* m = MemberOf(e, scope);
  return m != nullptr ? MemberOwnType(*m, scope.typedefs) : nullptr;
}

const DataType* DeclaredTypeOf(const Expr* e, const ValueScope& scope) {
  switch (e->kind) {
    case ExprKind::kIdentifier:
      return DeclaredTypeOfName(e->text, scope);
    case ExprKind::kSelect:
      return ElementDeclaredType(ExprIdent(e->base), scope);
    case ExprKind::kMemberAccess:
      return MemberDeclaredType(e, scope);
    default:
      return nullptr;
  }
}

const DataType* AggregateOf(const Expr* e, const ValueScope& scope) {
  const DataType* declared = DeclaredTypeOf(e, scope);
  if (declared == nullptr) return nullptr;
  const DataType* own = Resolved(*declared, scope);
  return own != nullptr && (own->kind == DataTypeKind::kStruct ||
                            own->kind == DataTypeKind::kUnion)
             ? own
             : nullptr;
}

ValueKind KindOfMemberSelect(const Expr* e, const ValueScope& scope) {
  const StructMember* m = MemberOf(e, scope);
  if (m == nullptr) return ValueKind::kUnknown;
  if (!m->unpacked_dims.empty()) return ValueKind::kOther;
  const DataType* own = MemberOwnType(*m, scope.typedefs);
  if (own != nullptr) return KindOfType(*own, scope);
  return m->type_kind == DataTypeKind::kNamed
             ? KindOfTypeName(m->type_name, scope)
             : KindOfTypeKind(m->type_kind);
}

ValueKind KindOfSelect(const Expr* e, const ValueScope& scope) {
  std::vector<const Expr*> selects;
  const Expr* base = e;
  for (; base->kind == ExprKind::kSelect; base = base->base) {
    selects.push_back(base);
  }
  std::string_view name = ExprIdent(base);
  auto it = scope.arrays.find(name);
  if (it == scope.arrays.end()) {
    ValueKind whole = KindOfVariable(name, scope);
    return whole == ValueKind::kIntegral || whole == ValueKind::kString
               ? ValueKind::kIntegral
               : ValueKind::kUnknown;
  }
  size_t dims = it->second.num_unpacked_dims;
  if (selects.size() < dims) return ValueKind::kOther;
  bool slices = std::any_of(
      selects.end() - static_cast<std::ptrdiff_t>(dims), selects.end(),
      [](const Expr* s) { return s->index_end != nullptr; });
  if (slices) return ValueKind::kOther;
  return selects.size() == dims ? KindOfElement(it->second, scope)
                                : ValueKind::kIntegral;
}

ValueKind KindOfCast(const Expr* e, const ValueScope& scope) {
  if (e->text == "const") return KindOfValue(e->lhs, scope);
  std::string_view type = e->text.empty() ? ExprIdent(e->rhs) : e->text;
  ValueKind keyword = FindKind(kCastKeywords, type);
  if (keyword != ValueKind::kUnknown) return keyword;
  ValueKind named = KindOfTypeName(type, scope);
  return named != ValueKind::kUnknown ? named : ValueKind::kIntegral;
}

ValueKind KindOfCall(const Expr* call, const ValueScope& scope) {
  if (call->lhs == nullptr) return ValueKind::kUnknown;
  if (call->lhs->kind == ExprKind::kMemberAccess) {
    return FindKind(kStringMethods, call->lhs->rhs->text);
  }
  auto it = scope.functions.find(ExprIdent(call->lhs));
  const ModuleItem* fn = it != scope.functions.end() ? it->second : nullptr;
  return fn != nullptr ? KindOfType(fn->return_type, scope)
                       : ValueKind::kUnknown;
}

ValueKind KindOfBinary(const Expr* e, const ValueScope& scope) {
  if (std::ranges::find(kArithmeticOps, e->op) == kArithmeticOps.end()) {
    return ValueKind::kIntegral;
  }
  ValueKind lhs = KindOfValue(e->lhs, scope);
  ValueKind rhs = KindOfValue(e->rhs, scope);
  return lhs == ValueKind::kReal || rhs == ValueKind::kReal
             ? ValueKind::kReal
             : ValueKind::kIntegral;
}

ValueKind KindOfUnary(const Expr* e, const ValueScope& scope) {
  ValueKind operand = KindOfValue(e->lhs, scope);
  if (operand == ValueKind::kUnknown || operand == ValueKind::kReal) {
    return operand;
  }
  return ValueKind::kIntegral;
}

ValueKind KindOfConcatenation(const Expr* e, const ValueScope& scope) {
  bool all_integral = true;
  for (const Expr* element : e->elements) {
    ValueKind kind = KindOfValue(element, scope);
    if (kind == ValueKind::kString) return ValueKind::kString;
    all_integral = all_integral && kind == ValueKind::kIntegral;
  }
  return all_integral ? ValueKind::kIntegral : ValueKind::kUnknown;
}

}  // namespace

const StructMember* SelectedStructMember(const Expr* e,
                                         const ValueScope& scope) {
  return MemberOf(e, scope);
}

ValueKind KindOfElement(const ElaboratorData::VarArrayInfo& info,
                        const ValueScope& scope) {
  if (info.elem_is_unpacked_aggregate) return ValueKind::kOther;
  if (info.elem_type == DataTypeKind::kNamed) {
    return KindOfTypeName(info.elem_type_name, scope);
  }
  return KindOfTypeKind(info.elem_type);
}

ValueKind KindOfValue(const Expr* e, const ValueScope& scope) {
  switch (e->kind) {
    case ExprKind::kIntegerLiteral:
      return ValueKind::kIntegral;
    case ExprKind::kRealLiteral:
      return ValueKind::kReal;
    case ExprKind::kIdentifier:
      return KindOfVariable(e->text, scope);
    case ExprKind::kUnary:
      return KindOfUnary(e, scope);
    case ExprKind::kBinary:
      return KindOfBinary(e, scope);
    case ExprKind::kCall:
      return KindOfCall(e, scope);
    case ExprKind::kSelect:
      return KindOfSelect(e, scope);
    case ExprKind::kMemberAccess:
      return KindOfMemberSelect(e, scope);
    case ExprKind::kCast:
      return KindOfCast(e, scope);
    case ExprKind::kConcatenation:
      return KindOfConcatenation(e, scope);
    default:
      return ValueKind::kUnknown;
  }
}

}  // namespace delta
