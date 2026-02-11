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

// §20.7 Array query functions ($dimensions, $left, $right, etc.)
Logic4Vec EvalArrayQuerySysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                std::string_view name);

// §20.11-20.16 Assertion control, sampled values, coverage, stochastic, PLA.
Logic4Vec EvalVerifSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                           std::string_view name);

// §6.16 String method dispatch (eval_string.cpp).
bool TryEvalStringMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                             Logic4Vec& out);

// §6.19 Enum method dispatch (eval_enum.cpp).
bool TryEvalEnumMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out);

// Extended expression evaluators (eval_expr.cpp).
Logic4Vec EvalReplicate(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalPrefixUnary(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalPostfixUnary(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalMemberAccess(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalCast(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalInside(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalStreamingConcat(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalAssignmentPattern(const Expr* expr, SimContext& ctx,
                                Arena& arena);
Logic4Vec EvalMatches(const Expr* expr, SimContext& ctx, Arena& arena);

// String <-> Logic4Vec conversion (eval_string.cpp).
Logic4Vec StringToLogic4Vec(Arena& arena, std::string_view str);

// Extract var_name and method_name from a kCall with kMemberAccess lhs.
// Returns false if the expression is not a method call pattern.
struct MethodCallParts {
  std::string_view var_name;
  std::string_view method_name;
};
bool ExtractMethodCallParts(const Expr* expr, MethodCallParts& out);

// Shared formatting helpers (eval_format.cpp).
std::string FormatDisplay(const std::string& fmt,
                          const std::vector<Logic4Vec>& vals);
std::string FormatArg(const Logic4Vec& val, char spec);
std::string FormatValueAsString(const Logic4Vec& val);
std::string ExtractFormatString(const Expr* first_arg);

}  // namespace delta
