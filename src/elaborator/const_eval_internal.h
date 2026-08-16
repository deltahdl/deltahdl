#pragma once

#include <cstdint>
#include <optional>
#include <string>
#include <vector>

#include "common/types.h"
#include "elaborator/const_eval.h"
#include "parser/ast.h"

namespace delta {

struct ConstVal {
  int64_t value;
  uint32_t width;
  bool is_signed;
};

std::optional<ConstVal> ConstEvalBinaryFull(const Expr* expr,
                                            const ScopeMap& scope);
std::optional<ConstVal> ConstEvalFull(const Expr* expr, const ScopeMap& scope);
std::optional<ConstVal> ConstEvalLiteral(const Expr* expr);
std::optional<ConstVal> ConstEvalStringLiteral(const Expr* expr);
std::optional<ConstVal> ConstEvalUnaryFull(const Expr* expr,
                                           const ScopeMap& scope);
std::optional<int64_t> EvalConcat(const Expr* expr, const ScopeMap& scope);
std::optional<int64_t> EvalConstSysCall(const Expr* expr,
                                        const ScopeMap& scope);
std::optional<int64_t> EvalReplicate(const Expr* expr, const ScopeMap& scope);

std::optional<ConstVal> ConstEvalSelectFull(const Expr* expr,
                                            const ScopeMap& scope);

// §11.5.1: the packed range the parameter `name` was declared with, taken from
// the module a live ParamRangeRegistryGuard installed. Empty when no guard is
// live, when the module declares no such parameter, or when that parameter's
// declaration carries no packed range -- in each of those cases the value is
// addressed as [width-1:0], where an index and a bit offset are the same
// number.
std::optional<PackedRange> RegisteredParamRange(std::string_view name);

// The module a live ParamRangeRegistryGuard installed, or null when none is
// live. A ScopeMap gives a name a value and says nothing about how it was
// declared, so this is what a fold consults when the declaration is what
// decides the answer.
const RtlirModule* RegisteredModule();

// Whether every element of `elems` is a constant expression. Vacuously true for
// an empty list, which is what an argument-list test alone answers for a call
// that takes no arguments.
bool AllElementsConstant(const std::vector<Expr*>& elems,
                         const ScopeMap& scope);

// §11.2.1: the value of a constant built-in method call (§5.13), evaluated at
// elaboration time from the declaration behind the operand. Empty when `expr`
// is not a built-in method call and when it is one this implementation cannot
// evaluate; the two are not distinguished, because a call that does not
// evaluate is not one a constant expression may hold.
std::optional<ConstVal> ConstEvalBuiltinMethodFull(const Expr* expr);

// Whether `expr` is a constant built-in method call, or empty when it is not a
// built-in method call at all. The empty answer is what lets a member access
// spelling one of the method names fall through to the ordinary compound
// parameter lookup, since a class may declare a parameter called `size`.
std::optional<bool> BuiltinMethodCallIsConstant(const Expr* expr,
                                                const ScopeMap& scope);

}  // namespace delta
