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

// §20.8 Math system calls ($ln, $log10, $sin, $pow, etc.)
Logic4Vec EvalMathSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                          std::string_view name);

// §21.3 Extended file I/O ($fgets, $fgetc, $feof, $fseek, etc.)
Logic4Vec EvalFileIOSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                            std::string_view name);

// §6.16 String method dispatch (eval_string.cpp).
bool TryEvalStringMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                             Logic4Vec& out);

// §6.19 Enum method dispatch (eval_enum.cpp).
bool TryEvalEnumMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out);

// Extended expression evaluators (eval_expr.cpp).
Logic4Vec EvalReplicate(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalPostfixUnary(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalMemberAccess(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalCast(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalInside(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalStreamingConcat(const Expr* expr, SimContext& ctx, Arena& arena);

// Shared formatting helper (used by eval.cpp and eval_systask.cpp).
std::string FormatDisplay(const std::string& fmt,
                          const std::vector<Logic4Vec>& vals);

// Extract format string from a string literal expression.
std::string ExtractFormatString(const Expr* first_arg);

}  // namespace delta
