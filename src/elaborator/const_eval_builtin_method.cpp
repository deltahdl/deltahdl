// §11.2.1 constant built-in method calls: the one place that decides whether a
// call to a §5.13 built-in method is a constant expression, and the one place
// that evaluates it. Both answers live here because they are the same answer.
// §11.2.1 has such a call, in a constant expression, evaluated during
// elaboration (printed page 270 of IEEE 1800-2023), so a call this file cannot
// evaluate is not one a constant expression may hold. Splitting the two apart
// is what let an expression be admitted wherever a constant expression is
// required and then fold to no value, leaving the declaration silently
// unresolved rather than either folded or reported.

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string_view>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/rtlir_enum_member.h"
#include "elaborator/rtlir_scopes.h"
#include "parser/ast_expr.h"

namespace delta {
namespace {

// The built-in methods of the data types: §6.16's string methods, §6.19.5's
// enumeration methods, and the array methods of §7.5 (dynamic arrays), §7.9
// (associative arrays), §7.10 (queues) and §7.12 (array manipulation). A call
// of one of them is constant only as §11.2.1 says -- no side effects, a value
// depending on its arguments and, unless it depends on nothing else, a
// constant identifier -- and §11.2.1 has a constant one evaluated at
// elaboration. Routing every one of them here, rather than through
// IsConstantExpr's argument test, is what keeps a mutating call such as
// `q.pop_front()` or a value-reading one such as `c.next()` on a variable,
// whose argument lists are empty and so pass that test, out of a constant
// expression: a call this file does not evaluate is not one a constant
// expression may hold.
//
// The names an earlier revision of this list carried -- bits, dimensions,
// unpacked_dimensions, left, right, low, high and increment -- name no built-in
// method. §7.11 rules them system functions, the array query functions $left,
// $right, $low, $high, $increment, $size, $dimensions and $unpacked_dimensions
// (printed page 173), and §20.6.2 gives $bits the same form. A name written
// without its $ is not one of them, so an expression spelling one is an
// ordinary member access and is decided as one.
constexpr std::array<std::string_view, 53> kBuiltinMethodNames = {
    // §6.16
    "len", "putc", "getc", "toupper", "tolower", "compare", "icompare",
    "substr", "atoi", "atohex", "atooct", "atobin", "atoreal", "itoa", "hextoa",
    "octtoa", "bintoa", "realtoa",
    // §6.19.5
    "first", "last", "next", "prev", "num", "name",
    // §7.5, §7.9, §7.10
    "size", "delete", "exists", "insert", "pop_front", "pop_back", "push_front",
    "push_back",
    // §7.12
    "find", "find_index", "find_first", "find_first_index", "find_last",
    "find_last_index", "min", "max", "unique", "unique_index", "reverse",
    "sort", "rsort", "shuffle", "sum", "product", "and", "or", "xor",
    // §7.12.4's iterator index query and §7.12.5's array map
    "index", "map"};

bool IsBuiltinMethodName(std::string_view method) {
  return std::ranges::find(kBuiltinMethodNames, method) !=
         kBuiltinMethodNames.end();
}

}  // namespace

// The member access a built-in method call is written through. `q.size()`
// parses as a call whose left operand is the access, and §5.13 makes the
// parentheses optional -- a built-in method call with no arguments may leave
// out the empty () after the subroutine name -- so `q.size` parses as the
// access itself. Null when the expression is neither shape, or when the member
// it names is not a built-in method.
const Expr* BuiltinMethodMember(const Expr* expr) {
  if (!expr) return nullptr;
  const Expr* member = nullptr;
  if (expr->kind == ExprKind::kCall && expr->lhs &&
      expr->lhs->kind == ExprKind::kMemberAccess) {
    member = expr->lhs;
  } else if (expr->kind == ExprKind::kMemberAccess) {
    member = expr;
  } else {
    return nullptr;
  }
  // `p::name()` calls a subroutine of package or class p, never a built-in
  // method, whatever it is called.
  if (member->is_scope_resolution || !member->rhs ||
      member->rhs->kind != ExprKind::kIdentifier)
    return nullptr;
  if (!IsBuiltinMethodName(member->rhs->text)) return nullptr;
  return member;
}

namespace {

// The variable the installed module declares under `name`, or null when no
// ParamRangeRegistryGuard is live or that module declares no such variable. The
// module is what carries a declaration; a ScopeMap is
// std::unordered_map<std::string_view, int64_t> and carries a value.
const RtlirVariable* RegisteredVariable(std::string_view name) {
  const RtlirModule* mod = RegisteredModule();
  if (!mod) return nullptr;
  for (const auto& var : mod->variables) {
    if (var.name == name) return &var;
  }
  return nullptr;
}

// The members of the enumeration the variable `operand` names was declared
// with, in declaration order. §6.19.5's first(), last() and num() (printed
// pages 123–124) answer from these alone -- the enumeration's first member, its
// last, and how many there are -- and not from the value the variable holds,
// which is exactly what §11.2.1 asks of a call admitted with a non-constant
// identifier: a method whose result never depends on what the identifier
// currently holds.
//
// Null for an operand that is not a bare identifier, for a variable of no
// enumerated type, and for a name the installed module does not declare. A
// declaration written `enum {red, green} c;` keys mod->enum_types by the
// variable's own name and a declaration written through a typedef keys it by
// the typedef's, and RtlirVariable::enum_type_name holds whichever of the two
// it is.
const std::vector<RtlirEnumMember>* EnumMembers(const Expr* operand) {
  if (!operand || operand->kind != ExprKind::kIdentifier) return nullptr;
  const RtlirVariable* var = RegisteredVariable(operand->text);
  if (!var || var->enum_type_name.empty()) return nullptr;
  const RtlirModule* mod = RegisteredModule();
  auto it = mod->enum_types.find(var->enum_type_name);
  if (it == mod->enum_types.end()) return nullptr;
  return &it->second;
}

// §6.16.1: str.len() gives the string's length, its count of characters
// (printed page 114). The count is taken from RtlirParamDecl::resolved_string
// rather than from RtlirParamDecl::resolved_value, because §6.16 lets a string
// be any length without truncation while resolved_value is 64 bits. §11.10
// packs a string literal one byte per character, so a value of more than eight
// characters has already lost bytes, and a length computed from it would be
// wrong for exactly the strings §6.16 admits.
//
// Empty for an operand that is not a bare identifier, for a name the installed
// module declares no parameter under, and for a parameter that took a value of
// some other type. §5.13 ties each built-in method to a particular data type,
// and it associates len() with string alone.
//
// Unlike num() on an enumeration, this value depends on the current value of
// the identifier, so §11.2.1 admits it only under its first rule, which
// requires the identifier itself to be a constant expression. A parameter is
// one: §11.2.1 lists "parameters" among the operands a constant expression
// consists of.
std::optional<std::string_view> StringParamValue(const Expr* operand) {
  if (!operand || operand->kind != ExprKind::kIdentifier) return std::nullopt;
  const RtlirModule* mod = RegisteredModule();
  if (!mod) return std::nullopt;
  for (const auto& param : mod->params) {
    if (param.name != operand->text) continue;
    // §23.9 puts a parameter a generate block declares in a scope of its own,
    // so a call written outside that block is not naming it however the names
    // agree. RegisteredGenPrefixes() is where the call stands.
    if (!ParamVisibleFromScopes(param.gen_block_prefix,
                                RegisteredGenPrefixes()))
      continue;
    if (!param.is_string_value) return std::nullopt;
    return param.resolved_string;
  }
  return std::nullopt;
}

// §6.16.3: str.getc(i) answers the ASCII code of the character at index i, and
// 0 for an index outside the string (printed page 115). Its prototype returns
// `byte`, a signed 8-bit integer (§6.11.1).
std::optional<ConstVal> StringParamChar(const Expr* call, std::string_view str,
                                        const ScopeMap& scope) {
  if (call->kind != ExprKind::kCall || call->args.size() != 1)
    return std::nullopt;
  auto index = ConstEvalInt(call->args[0], scope);
  if (!index) return std::nullopt;
  const bool kInside =
      *index >= 0 && static_cast<uint64_t>(*index) < str.size();
  const int64_t kCode =
      kInside ? static_cast<int8_t>(str[static_cast<size_t>(*index)]) : 0;
  return ConstVal{kCode, 8, true};
}

}  // namespace

std::optional<ConstVal> ConstEvalBuiltinMethodFull(const Expr* expr,
                                                   const ScopeMap& scope) {
  const Expr* member = BuiltinMethodMember(expr);
  if (!member) return std::nullopt;
  const std::string_view kMethod = member->rhs->text;
  if (kMethod == "getc") {
    auto str = StringParamValue(member->lhs);
    if (!str) return std::nullopt;
    return StringParamChar(expr, *str, scope);
  }
  // §6.16.1, §6.19.5.1, §6.19.5.2 and §6.19.5.5 give len(), first(), last() and
  // num() an empty parameter list. An argument list written on one of them
  // names it as something other than the built-in method.
  if (expr->kind == ExprKind::kCall && !expr->args.empty()) return std::nullopt;
  if (kMethod == "len") {
    auto str = StringParamValue(member->lhs);
    if (!str) return std::nullopt;
    // §6.16.1 gives the prototype `function int len();`, which §6.11.1 makes a
    // 32-bit signed integer.
    return ConstVal{static_cast<int64_t>(str->size()), 32, true};
  }
  // Every other built-in method stops here unfolded, size() among them: this
  // file answers a built-in method from the declaration behind its operand,
  // and RtlirParamDecl records an integer, a real and a string and no array,
  // so there is no element count to read. Leaving a method unfolded is what
  // keeps it out of a constant expression rather than answered wrongly.
  const std::vector<RtlirEnumMember>* members = EnumMembers(member->lhs);
  // A.2.2.1 gives an enumeration at least one member, so front() and back()
  // name one.
  if (members == nullptr) return std::nullopt;
  // §6.19.5.5 declares num() as returning `int`, a 32-bit signed integer
  // (§6.11.1); first() and last() return the enumeration's own type, whose
  // members' values are what the declaration gave them.
  if (kMethod == "num")
    return ConstVal{static_cast<int64_t>(members->size()), 32, true};
  if (kMethod == "first") return ConstVal{members->front().value, 32, true};
  if (kMethod == "last") return ConstVal{members->back().value, 32, true};
  return std::nullopt;
}

std::optional<bool> BuiltinMethodCallIsConstant(const Expr* expr,
                                                const ScopeMap& scope) {
  if (!BuiltinMethodMember(expr)) return std::nullopt;
  // §11.2.1 requires the input arguments to be constant expressions whichever
  // of its two rules admits the call, so this is tested before the operand.
  if (!AllElementsConstant(expr->args, scope)) return false;
  // §11.2.1: such a call in a constant expression is evaluated during
  // elaboration. The answer is therefore whether ConstEvalBuiltinMethodFull
  // evaluates it, which keeps this predicate and that folder from disagreeing
  // about one expression.
  //
  // This is stricter than §11.2.1's first rule, which admits a call whose
  // identifier and input arguments are constant expressions, and deliberately
  // so. That rule governs calls to the built-in methods of §5.13, and a
  // ScopeMap says a name has an integer value without saying what it was
  // declared as. §5.13 ties each built-in method to a particular data type, and
  // it associates none with an integer, so a ScopeMap-constant identifier
  // carries no built-in method for the rule to admit. The folder answers
  // `len()` on a string parameter from the characters recorded on its
  // declaration rather than from a ScopeMap, so that call is admitted here.
  // What remains unfolded is a built-in method whose operand's declaration
  // carries no value the folder can read; reporting it is what tells its author
  // the value was not computed.
  return ConstEvalBuiltinMethodFull(expr, scope).has_value();
}

}  // namespace delta
