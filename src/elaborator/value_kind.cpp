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

// §6.16.1 to §6.16.15: the kind of value each string method gives.
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

// §6.24.1: the casting types written as a keyword, by the kind of value the
// cast gives. signed and unsigned (§6.24.1) change only the signedness, of an
// integral value.
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

// The kind of value a type left as the name `name` gives: a class handle has
// none of the operators, and a typedef gives what it stands for.
ValueKind KindOfTypeName(std::string_view name, const ValueScope& scope);

// The type `type` stands for, through every typedef name it is written with;
// null where a name resolves to no typedef.
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

// Whether `name` is the with expression's iterator, which hides any variable
// of that name.
bool IsIterator(std::string_view name, const ValueScope& scope) {
  return !name.empty() && name == scope.iterator.name;
}

// A variable written alone: the iterator is an element of its array, a whole
// unpacked array has none of the operators, and any other variable is of the
// type it is declared with.
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

// The structure or union an operand of a member select is, where a
// declaration says: the iterator, an element of a one-dimensional array or a
// variable declared with a typedef name, or a member that is one in turn.
const DataType* AggregateOf(const Expr* e, const ValueScope& scope);

// The member `name` of the structure or union `aggregate`; null where it has
// none of that name.
const StructMember* MemberNamed(const DataType& aggregate,
                                std::string_view name) {
  auto it =
      std::ranges::find(aggregate.struct_members, name, &StructMember::name);
  return it != aggregate.struct_members.end() ? &*it : nullptr;
}

// The member the member select `e` names, where AggregateOf traces its
// operand; null where it does not, or the operand has no member of that name.
const StructMember* MemberOf(const Expr* e, const ValueScope& scope) {
  const DataType* outer = AggregateOf(e->lhs, scope);
  return outer != nullptr ? MemberNamed(*outer, e->rhs->text) : nullptr;
}

// The type the iterator's elements, or the variable `name`, is declared with
// when that is a typedef name; null otherwise.
const DataType* DeclaredTypeOfName(std::string_view name,
                                   const ValueScope& scope) {
  if (IsIterator(name, scope)) return scope.iterator.array->elem_data_type;
  auto named = scope.var_named_types.find(name);
  if (named == scope.var_named_types.end()) return nullptr;
  auto td = scope.typedefs.find(named->second);
  return td != scope.typedefs.end() ? &td->second : nullptr;
}

// The type the elements of the one-dimensional array `name` are declared with;
// null for an array of more dimensions and for a name that is no array.
const DataType* ElementDeclaredType(std::string_view name,
                                    const ValueScope& scope) {
  auto it = scope.arrays.find(name);
  return it != scope.arrays.end() && it->second.num_unpacked_dims == 1
             ? it->second.elem_data_type
             : nullptr;
}

// The type the member the member select `e` names is written with, through
// typedef names; null where MemberOf finds no member.
const DataType* MemberDeclaredType(const Expr* e, const ValueScope& scope) {
  const StructMember* m = MemberOf(e, scope);
  return m != nullptr ? MemberOwnType(*m, scope.typedefs) : nullptr;
}

// The declared type of the operand `e` of a member select, before typedef
// names are followed: a variable's or the iterator's, an element's of a
// one-dimensional array, or a member's.
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

// §7.2: a member select gives the member's type, and a member that is itself
// an unpacked array has none of the operators.
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

// §7.4.3 and §11.5.1: a select through every unpacked dimension of an array
// gives an element, and a further select a bit or part of one; a select
// through fewer, or a slice of an unpacked dimension, gives an array. A bit or
// part select of an integral variable or a string's character select (§6.16)
// is integral.
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
  // `selects` runs outward in, so the select nearest the name is last.
  bool slices = std::any_of(
      selects.end() - static_cast<std::ptrdiff_t>(dims), selects.end(),
      [](const Expr* s) { return s->index_end != nullptr; });
  if (slices) return ValueKind::kOther;
  return selects.size() == dims ? KindOfElement(it->second, scope)
                                : ValueKind::kIntegral;
}

// §6.24.1: a cast gives its casting type, written as a keyword (cast->text) or
// as an expression (cast->rhs), which is a type name or else a size, giving an
// integral value. const changes nothing about the value.
ValueKind KindOfCast(const Expr* e, const ValueScope& scope) {
  if (e->text == "const") return KindOfValue(e->lhs, scope);
  std::string_view type = e->text.empty() ? ExprIdent(e->rhs) : e->text;
  ValueKind keyword = FindKind(kCastKeywords, type);
  if (keyword != ValueKind::kUnknown) return keyword;
  ValueKind named = KindOfTypeName(type, scope);
  return named != ValueKind::kUnknown ? named : ValueKind::kIntegral;
}

// A method call is the call of a member access, of which this reads the string
// methods; a call of a function gives the function's return type; and `new`,
// which the parser reads as a call, has no callee at all.
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
