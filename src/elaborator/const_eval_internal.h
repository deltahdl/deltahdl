#pragma once

#include <cstdint>
#include <optional>
#include <string>

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

}  // namespace delta
