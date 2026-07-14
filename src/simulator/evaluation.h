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

// §5.7.1/§11.6.1 — the self-determined bit length of an integer literal from
// its text (sized literals carry an explicit width; an unsized decimal literal
// is at least 32 bits, 64 when its value exceeds 32 bits).
uint32_t LiteralWidth(std::string_view text, uint64_t val);

bool HasUnknownBits(const Logic4Vec& v);
Logic4Vec MakeAllX(Arena& arena, uint32_t width);
int64_t SignExtend(uint64_t val, uint32_t width);

// §7.8.1/§7.8.4 — canonicalize an integral associative-array index into its
// map key. A wildcard index ([*]) is self-determined and treated as unsigned:
// leading zeros are dropped and the minimal numeric value is used, so equal
// values of differing widths collapse to one entry. A typed integral index is
// cast to its index width: sign-extended when the index type is signed and
// zero-extended when it is unsigned, which fixes the key ordering.
int64_t AssocIntKey(const Logic4Vec& val, bool is_wildcard,
                    uint32_t index_width, bool is_signed = true);

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
// Evaluates `lhs inside { elem }` for one set member, returning 1 for a match,
// 0 for a definite mismatch, and 2 when the comparison is ambiguous (x). Shared
// with the case-inside statement path so both apply the same §11.4.6/§11.4.13
// asymmetric wildcard matching.
int EvalInsideElement(const Logic4Vec& lhs, const Expr* elem, SimContext& ctx,
                      Arena& arena);
Logic4Vec EvalStreamingConcat(const Expr* expr, SimContext& ctx, Arena& arena);
// §20.9: pack a bit-vector system function's expression operand into the packed
// vector {>>{expression}} would produce (§11.4.14), so an aggregate bit-stream
// argument contributes all of its bits when its ones/unknown bits are counted.
Logic4Vec PackBitStreamOperand(const Expr* arg, SimContext& ctx, Arena& arena);
Logic4Vec EvalAssignmentPattern(const Expr* expr, SimContext& ctx,
                                Arena& arena);

Logic4Vec EvalStructPattern(const Expr* expr, const StructTypeInfo* info,
                            SimContext& ctx, Arena& arena);
// §10.9.2: evaluate a structure assignment pattern (keyed or positional)
// against a known struct layout, coercing each member expression to the
// corresponding member's type/width. Falls back to width-summing concatenation
// for the replication form and for structs wider than a single word.
Logic4Vec EvalStructPatternValue(const Expr* expr, const StructTypeInfo* info,
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

// §11.12 — expand a let into its body expression. `call` supplies the actual
// arguments (it may be a bare identifier reference for a no-argument let, in
// which case no actuals are bound).
Logic4Vec EvalLetExpansion(ModuleItem* decl, const Expr* call, SimContext& ctx,
                           Arena& arena);

void EmitSeverityHeader(SimContext& ctx, std::string_view prefix,
                        std::string_view msg, std::ostream& os,
                        uint32_t line = 0);

const ModuleItem* SetupTaskCall(const Expr* expr, SimContext& ctx,
                                Arena& arena);
void TeardownTaskCall(const ModuleItem* func, const Expr* expr, SimContext& ctx,
                      Arena& arena);

Logic4Vec EvalClassNew(std::string_view class_type, const Expr* new_expr,
                       SimContext& ctx, Arena& arena);

// Bind the specialization parameters of a parameterized class scope (e.g. the
// N in E#(.N(77))) as local variables so the constructor/method body sees the
// overridden values. base_id is the identifier carrying the #(...) overrides in
// its elements.
struct ClassTypeInfo;
void BindClassParams(const ClassTypeInfo* cls, const Expr* base_id,
                     SimContext& ctx, Arena& arena);

void ApplyClassParamOverrides(std::string_view var_name, uint64_t handle,
                              SimContext& ctx, Arena& arena);

class DiagEngine;
struct ModuleItem;
void ValidateRefLifetime(const ModuleItem* func, DiagEngine& diag);

void ValidateConstRefWriteProtection(const ModuleItem* func, DiagEngine& diag);

Logic4Vec StringToLogic4Vec(Arena& arena, std::string_view str);

// Decode a packed string value (byte per octet, high-order byte first) back to
// a std::string, dropping NUL padding. The inverse of StringToLogic4Vec, used
// where a string-typed argument must be read as raw bytes (e.g. an RNG state
// string handed to set_randstate()).
std::string Logic4VecToString(const Logic4Vec& vec);

struct MethodCallParts {
  std::string_view var_name;
  std::string_view method_name;
};
bool ExtractMethodCallParts(const Expr* expr, MethodCallParts& out);

// §21.2: the optional rendering inputs a display task threads into
// FormatDisplay alongside the format string and its value list. Each member
// backs a format specifier that draws on something other than the raw value
// stream: `p_fmts` carries the precomputed %p assignment-pattern strings,
// `v_fmts` the precomputed %v net-strength strings (§21.2.1.4), `time_format`
// the $timeformat configuration for %t (§20.4.3), and `ctx` the run-time
// context %m / %l need to name the invoking scope (§21.2.1.5, §33.7). A null
// vector pointer means "no precomputed strings"; every member defaults so an
// ordinary "%d"-style call passes only fmt and vals.
struct DisplayFormatOpts {
  const std::vector<std::string>* p_fmts = nullptr;
  const TimeFormatSpec* time_format = nullptr;
  const std::vector<std::string>* v_fmts = nullptr;
  SimContext* ctx = nullptr;
  // §21.2.1.1: one flag per positional value argument marking it as an unpacked
  // aggregate, so an integer format specifier that consumes such an argument
  // can be rejected. A null pointer means the caller supplied no type
  // information.
  const std::vector<char>* arg_unpacked_agg = nullptr;
};

// §21.2.1.5: the %m specifier prints the hierarchical name of the scope that
// invokes the display task. Rendering it requires the run-time context, so an
// optional SimContext is threaded through `opts`; when null (no simulation
// context), %m yields nothing.
std::string FormatDisplay(const std::string& fmt,
                          const std::vector<Logic4Vec>& vals,
                          const DisplayFormatOpts& opts = {});
std::string FormatArg(const Logic4Vec& val, char spec);
std::string FormatStrength(const NetStrength& ns);
std::string FormatTimeUnderTimeformat(const Logic4Vec& val,
                                      const TimeFormatSpec& spec);
std::string FormatValueAsString(const Logic4Vec& val);
std::string ExtractFormatString(const Expr* first_arg);

Logic4Vec EvalUnbasedUnsized(const Expr* expr, Arena& arena);
Logic4Vec EvalIntLiteral(const Expr* expr, Arena& arena);
Logic4Vec EvalStringLiteral(const Expr* expr, Arena& arena);

}  // namespace delta
