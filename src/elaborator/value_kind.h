#pragma once

#include <cstdint>
#include <string_view>
#include <unordered_map>
#include <unordered_set>

#include "elaborator/elaborator_data.h"
#include "elaborator/type_eval.h"
#include "parser/ast_type.h"

namespace delta {

struct Expr;
struct ModuleItem;

// The kinds of value the rules on associative indices (§7.8.1 to §7.8.4) and
// on the operations array methods apply (§7.12.1 to §7.12.3) turn on. kOther is
// a value with none of the operators: a class handle, a chandle, an event, an
// unpacked structure or union, or an unpacked array.
enum class ValueKind : uint8_t { kUnknown, kIntegral, kReal, kString, kOther };

// §7.12: the name an array method's with expression gives each element as it
// is visited, and the array whose elements those are. An empty name binds none.
struct ValueIterator {
  std::string_view name;
  const ElaboratorData::VarArrayInfo* array = nullptr;
};

// What KindOfValue reads to type an expression: each variable's declared kind
// and, where that kind is a name, the name; the unpacked arrays; the functions;
// the typedefs and classes the names stand for; and the iterator in scope.
struct ValueScope {
  const std::unordered_map<std::string_view, DataTypeKind>& var_types;
  const std::unordered_map<std::string_view, std::string_view>& var_named_types;
  const std::unordered_map<std::string_view, ElaboratorData::VarArrayInfo>&
      arrays;
  const std::unordered_map<std::string_view, const ModuleItem*>& functions;
  const TypedefMap& typedefs;
  const std::unordered_set<std::string_view>& class_names;
  ValueIterator iterator = {};
};

// The kind of value a type written as `kind` gives, a name aside.
ValueKind KindOfTypeKind(DataTypeKind kind);

// The kind of value the expression `e` gives, as far as its form and the
// declarations `scope` holds tell: a literal by its own kind; a variable, the
// iterator, an element select, a member select, a cast or a function call by
// the type declared for it; an arithmetic operator real when either operand
// is and integral otherwise, any other binary operator integral; a unary
// operator real over a real and integral over any other known kind; a string
// method by the result §6.16 gives it; and a concatenation a string when an
// element is one (§11.4.12.2) and integral when every element is integral.
// Anything else is kUnknown.
ValueKind KindOfValue(const Expr* e, const ValueScope& scope);

// The kind of value an element of the array `info` describes is.
ValueKind KindOfElement(const ElaboratorData::VarArrayInfo& info,
                        const ValueScope& scope);

// The member of a structure or union the member select `e` names, where the
// declarations `scope` holds trace its operand; null where they do not.
const StructMember* SelectedStructMember(const Expr* e,
                                         const ValueScope& scope);

}  // namespace delta
