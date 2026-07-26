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

}  // namespace delta
