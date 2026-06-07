#pragma once

#include <iosfwd>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "lexer/token.h"

namespace delta {

struct Expr;
struct ModuleItem;
struct StructTypeInfo;
struct TimeFormatSpec;
struct NetStrength;
class SimContext;
class Arena;

Logic4Vec EvalExpr(const Expr* expr, SimContext& ctx, Arena& arena,
                   uint32_t context_width = 0);

bool HasUnknownBits(const Logic4Vec& v);
Logic4Vec MakeAllX(Arena& arena, uint32_t width);
int64_t SignExtend(uint64_t val, uint32_t width);

// §7.8.1/§7.8.4 — canonicalize an integral associative-array index into its
// map key. A wildcard index ([*]) is self-determined and treated as unsigned:
// leading zeros are dropped and the minimal numeric value is used, so equal
// values of differing widths collapse to one entry. A typed integral index is
// cast to its index width: sign-extended when the index type is signed and
// zero-extended when it is unsigned, which fixes the key ordering.
int64_t AssocIntKey(const Logic4Vec& val, bool is_wildcard, uint32_t index_width,
                    bool is_signed = true);

Logic4Vec EvalSelect(const Expr* expr, SimContext& ctx, Arena& arena);

Logic4Vec EvalUtilitySysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                             std::string_view name);

Logic4Vec EvalIOSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                        std::string_view name);

Logic4Vec EvalMathSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                          std::string_view name);

Logic4Vec EvalFileIOSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                            std::string_view name);

Logic4Vec EvalArrayQuerySysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                                std::string_view name);

Logic4Vec EvalVerifSysCall(const Expr* expr, SimContext& ctx, Arena& arena,
                           std::string_view name);

// §20.16 / §20.16.1: evaluate a PLA modeling system task. Returns false when
// the callee does not name one of the sixteen Table 20-12 tasks; otherwise it
// evaluates the array, drives the output terms, and (for the asynchronous
// forms) installs the change-driven re-evaluation watchers, returning true.
bool TryEvalPlaSystemTask(const Expr* expr, SimContext& ctx, Arena& arena);

bool TryEvalStringMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                             Logic4Vec& out);

bool TryEvalEnumMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out);
bool TryEvalEnumProperty(std::string_view var_name, std::string_view method,
                          SimContext& ctx, Arena& arena, Logic4Vec& out);

bool TryEvalArrayMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                            Logic4Vec& out);
bool TryExecArrayMethodStmt(const Expr* expr, SimContext& ctx, Arena& arena);

Logic4Vec AssembleConcatParts(const std::vector<Logic4Vec>& parts,
                              uint32_t total_width, Arena& arena);

Logic4Vec EvalBinaryOp(TokenKind op, Logic4Vec lhs, Logic4Vec rhs, Arena& arena,
                       uint32_t context_width = 0);

TokenKind CompoundAssignBaseOp(TokenKind op);
bool IsCompoundAssignOp(TokenKind op);
Logic4Vec EvalCompoundAssign(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalReplicate(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalPrefixUnary(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalPostfixUnary(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalMemberAccess(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalCast(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalInside(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalStreamingConcat(const Expr* expr, SimContext& ctx, Arena& arena);
Logic4Vec EvalAssignmentPattern(const Expr* expr, SimContext& ctx,
                                Arena& arena);

Logic4Vec EvalStructPattern(const Expr* expr, const StructTypeInfo* info,
                            SimContext& ctx, Arena& arena);
Logic4Vec EvalMatches(const Expr* expr, SimContext& ctx, Arena& arena);

Logic4Vec EvalSystemCall(const Expr* expr, SimContext& ctx, Arena& arena);

// §20.4.2: build the report line $printtimescale displays for `expr` against
// the timescale state in `ctx` (see eval_function.cpp for the format).
std::string BuildPrinttimescaleReport(const Expr* expr, SimContext& ctx);

// §20.17.2: assemble the call-stack text $stacktrace reports for the context
// invoking it, working from that context up to the top-level process. The
// content is implementation dependent (see eval_function.cpp for the format).
std::string BuildStackTraceReport(const SimContext& ctx);
Logic4Vec EvalFunctionCall(const Expr* expr, SimContext& ctx, Arena& arena);

void EmitSeverityHeader(SimContext& ctx, std::string_view prefix,
                        std::string_view msg, std::ostream& os);

const ModuleItem* SetupTaskCall(const Expr* expr, SimContext& ctx,
                                Arena& arena);
void TeardownTaskCall(const ModuleItem* func, const Expr* expr,
                      SimContext& ctx, Arena& arena);

Logic4Vec EvalClassNew(std::string_view class_type, const Expr* new_expr,
                       SimContext& ctx, Arena& arena);

void ApplyClassParamOverrides(std::string_view var_name, uint64_t handle,
                              SimContext& ctx, Arena& arena);

class DiagEngine;
struct ModuleItem;
void ValidateRefLifetime(const ModuleItem* func, DiagEngine& diag);

void ValidateConstRefWriteProtection(const ModuleItem* func, DiagEngine& diag);

Logic4Vec StringToLogic4Vec(Arena& arena, std::string_view str);

struct MethodCallParts {
  std::string_view var_name;
  std::string_view method_name;
};
bool ExtractMethodCallParts(const Expr* expr, MethodCallParts& out);

// §21.2.1.5: the %m specifier prints the hierarchical name of the scope that
// invokes the display task. Rendering it requires the run-time context, so an
// optional SimContext is threaded through; when null (no simulation context),
// %m yields nothing.
std::string FormatDisplay(const std::string& fmt,
                          const std::vector<Logic4Vec>& vals,
                          const std::vector<std::string>& p_fmts = {},
                          const TimeFormatSpec* time_format = nullptr,
                          const std::vector<std::string>& v_fmts = {},
                          SimContext* ctx = nullptr);
std::string FormatArg(const Logic4Vec& val, char spec);
std::string FormatStrength(const NetStrength& ns);
std::string FormatTimeUnderTimeformat(const Logic4Vec& val,
                                      const TimeFormatSpec& spec);
std::string FormatValueAsString(const Logic4Vec& val);
std::string ExtractFormatString(const Expr* first_arg);

Logic4Vec EvalUnbasedUnsized(const Expr* expr, Arena& arena);
Logic4Vec EvalIntLiteral(const Expr* expr, Arena& arena);
Logic4Vec EvalStringLiteral(const Expr* expr, Arena& arena);

}
