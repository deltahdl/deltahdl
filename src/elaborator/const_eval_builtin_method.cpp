// §11.2.1 constant built-in method calls: the one place that decides whether a
// call to a §5.13 built-in method is a constant expression, and the one place
// that evaluates it. Both answers live here because they are the same answer.
// §11.2.1 states of such a call that "when used in constant expressions, these
// function calls shall be evaluated at elaboration time" (printed page 270 of
// ~/LRM.pdf), so a call this file cannot evaluate is not one a constant
// expression may hold. Splitting the two apart is what let an expression be
// admitted wherever a constant expression is required and then fold to no
// value, leaving the declaration silently unresolved rather than either folded
// or reported.

#include <cstdint>
#include <optional>
#include <string_view>

#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {
namespace {

// The built-in methods §5.13 defines that return an integer: "dynamic_array.
// size, associative_array.num, and string.len" (printed page 87). §6.19.5.5
// adds num() on an enumeration, and §7.9 adds num() and size() on an
// associative array, so the three names cover every one of them.
//
// The names an earlier revision of this list also carried -- bits, dimensions,
// unpacked_dimensions, left, right, low, high and increment -- name no built-in
// method. §7.11 rules them system functions: "SystemVerilog provides system
// functions to return information about an array. These are $left, $right,
// $low, $high, $increment, $size, $dimensions, and $unpacked_dimensions"
// (printed page 173), and §20.6.2 gives $bits the same form. A name written
// without its $ is not one of them, so an expression spelling one is an
// ordinary member access and is decided as one.
//
// The list decides nothing further on its own. What it does is route a call
// away from IsConstantExpr's argument test, which would admit every one of
// these because their argument lists are empty; what each returns is then
// decided from the operand's declaration below.
bool IsBuiltinMethodName(std::string_view method) {
  return method == "size" || method == "num" || method == "len";
}

// The member access a built-in method call is written through. `q.size()`
// parses as a call whose left operand is the access, and §5.13 makes the
// parentheses optional -- "when a subroutine built-in method call specifies no
// arguments, the empty parentheses, (), following the subroutine name are
// optional" -- so `q.size` parses as the access itself. Null when the
// expression is neither shape, or when the member it names is not a built-in
// method.
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
  if (!member->rhs || member->rhs->kind != ExprKind::kIdentifier)
    return nullptr;
  if (!IsBuiltinMethodName(member->rhs->text)) return nullptr;
  return member;
}

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

// §6.19.5.5: "The num() method returns the number of elements in the given
// enumeration" (printed page 124). The count is a property of the enumeration
// the variable was declared with rather than of the value the variable holds,
// which is exactly what §11.2.1 asks of a call admitted with a non-constant
// identifier: a method "whose value does not depend on the current value of the
// identifier".
//
// Empty for an operand that is not a bare identifier, for a variable of no
// enumerated type, and for a name the installed module does not declare. A
// declaration written `enum {red, green} c;` keys mod->enum_types by the
// variable's own name and a declaration written through a typedef keys it by
// the typedef's, and RtlirVariable::enum_type_name holds whichever of the two
// it is.
std::optional<int64_t> EnumMemberCount(const Expr* operand) {
  if (!operand || operand->kind != ExprKind::kIdentifier) return std::nullopt;
  const RtlirVariable* var = RegisteredVariable(operand->text);
  if (!var || var->enum_type_name.empty()) return std::nullopt;
  const RtlirModule* mod = RegisteredModule();
  auto it = mod->enum_types.find(var->enum_type_name);
  if (it == mod->enum_types.end()) return std::nullopt;
  return static_cast<int64_t>(it->second.size());
}

// §6.16.1: "str.len() returns the length of the string, i.e., the number of
// characters in the string" (printed page 114). The count is taken from
// RtlirParamDecl::resolved_string rather than from
// RtlirParamDecl::resolved_value, because §6.16 rules that "strings can be of
// arbitrary length and no truncation occurs" while resolved_value is 64 bits.
// §11.10 packs a string literal one byte per character, so a value of more
// than eight characters has already lost bytes, and a length computed from it
// would be wrong for exactly the strings §6.16 admits.
//
// Empty for an operand that is not a bare identifier, for a name the installed
// module declares no parameter under, and for a parameter that took a value of
// some other type. §5.13 rules that "a built-in method can only be associated
// with a particular data type", and it associates len() with string alone.
//
// Unlike num() on an enumeration, this value depends on the current value of
// the identifier, so §11.2.1 admits it only under its first rule, which
// requires the identifier itself to be a constant expression. A parameter is
// one: §11.2.1 lists "parameters" among the operands a constant expression
// consists of.
std::optional<int64_t> StringParamLength(const Expr* operand) {
  if (!operand || operand->kind != ExprKind::kIdentifier) return std::nullopt;
  const RtlirModule* mod = RegisteredModule();
  if (!mod) return std::nullopt;
  for (const auto& param : mod->params) {
    if (param.name != operand->text) continue;
    // §23.9 puts a parameter a generate block declares in a scope of its own,
    // so a call written outside that block is not naming it however the names
    // agree. RegisteredGenPrefixes() is where the call stands.
    //
    // No test reaches this line with a generate block's parameter, and the two
    // that tried are recorded in #3226. A ParamRangeRegistryGuard has to be
    // live for RegisteredModule() to answer at all, and of the sites that open
    // one, the parameter port list is processed before any block's parameter
    // exists and a defparam right-hand side never reaches here: §23.10.1 admits
    // "only numbers and references to parameters" there, which a method call is
    // not. The UDP instance path is the route left to try.
    if (!ParamVisibleFromScopes(param.gen_block_prefix,
                                RegisteredGenPrefixes()))
      continue;
    if (!param.is_string_value) return std::nullopt;
    return static_cast<int64_t>(param.resolved_string.size());
  }
  return std::nullopt;
}

}  // namespace

std::optional<ConstVal> ConstEvalBuiltinMethodFull(const Expr* expr) {
  const Expr* member = BuiltinMethodMember(expr);
  if (!member) return std::nullopt;
  // §6.19.5.5 gives the prototype `function int num();`, and §5.13 and §7.9
  // give size(), num() and len() the same empty parameter list. An argument
  // list written on one of these names it as something other than the built-in
  // method.
  if (expr->kind == ExprKind::kCall && !expr->args.empty()) return std::nullopt;
  if (member->rhs->text == "len") {
    auto length = StringParamLength(member->lhs);
    if (!length) return std::nullopt;
    // §6.16.1 gives the prototype `function int len();`, which §6.11.1 makes a
    // 32-bit signed integer.
    return ConstVal{*length, 32, true};
  }
  // The third name IsBuiltinMethodName admits, size, stops here and is never
  // folded. §7.5 gives size() on a dynamic array and §7.9 gives num() and
  // size() on an associative array, and this file answers a built-in method
  // from the declaration behind its operand: RtlirParamDecl records an
  // integer, a real and a string, and no array, so there is no element count
  // here to read. Leaving size unfolded is what keeps it from being answered
  // wrongly, since a declaration this file cannot read is not one it can count.
  if (member->rhs->text != "num") return std::nullopt;
  auto count = EnumMemberCount(member->lhs);
  if (!count) return std::nullopt;
  // §6.19.5.5 declares num() as returning `int`, which §6.11.1 makes a 32-bit
  // signed integer.
  return ConstVal{*count, 32, true};
}

std::optional<bool> BuiltinMethodCallIsConstant(const Expr* expr,
                                                const ScopeMap& scope) {
  if (!BuiltinMethodMember(expr)) return std::nullopt;
  // §11.2.1 requires the input arguments to be constant expressions whichever
  // of its two rules admits the call, so this is tested before the operand.
  if (!AllElementsConstant(expr->args, scope)) return false;
  // §11.2.1: "when used in constant expressions, these function calls shall be
  // evaluated at elaboration time". The answer is therefore whether
  // ConstEvalBuiltinMethodFull evaluates it, which keeps this predicate and
  // that folder from disagreeing about one expression.
  //
  // This is stricter than §11.2.1's first rule, which admits a call whose
  // "identifier and input arguments are constant expressions", and deliberately
  // so. That rule governs calls "to built-in methods (see 5.13)", and a
  // ScopeMap says a name has an integer value without saying what it was
  // declared as. §5.13 rules that "a built-in method can only be associated
  // with a particular data type", and it associates none with an integer, so a
  // ScopeMap-constant identifier carries no built-in method for the rule to
  // admit. The folder answers `len()` on a string parameter from the characters
  // recorded on its declaration rather than from a ScopeMap, so that call is
  // admitted here. What remains unfolded is a built-in method whose operand's
  // declaration carries no value the folder can read; reporting it is what
  // tells its author the value was not computed.
  return ConstEvalBuiltinMethodFull(expr).has_value();
}

}  // namespace delta
