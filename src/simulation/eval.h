#pragma once

#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"

namespace delta {

struct Expr;
class SimContext;
class Arena;

Logic4Vec EvalExpr(const Expr* expr, SimContext& ctx, Arena& arena);

// §20 Utility system calls ($clog2, $bits, $countones, etc.)
Logic4Vec EvalUtilitySysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                             std::string_view name);

// §21 I/O system calls ($fopen, $fclose, $readmemh, etc.)
Logic4Vec EvalIOSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                        std::string_view name);

// Shared formatting helper (used by eval.cpp and eval_systask.cpp).
std::string FormatDisplay(const std::string& fmt,
                          const std::vector<Logic4Vec>& vals);

// Extract format string from a string literal expression.
std::string ExtractFormatString(const Expr* first_arg);

}  // namespace delta
