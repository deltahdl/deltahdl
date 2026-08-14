#pragma once

#include <iosfwd>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/source_loc.h"
#include "common/types.h"
#include "lexer/token.h"

namespace delta {

struct DataType;
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

// §6.12: a shortreal is a C float and a real is a C double, so the width of a
// real vector says which pattern it carries — 32 bits a float, any other width
// a double. This is the only correct way to read one back, and reading the
// bytes as a double regardless turns a shortreal into a subnormal near zero.
// The caller decides what a non-real vector contributes, so `v.is_real` shall
// hold.
double RealVecToDouble(const Logic4Vec& v);

// The inverse of RealVecToDouble: lays `val` into a real vector of the given
// width, rounding to single precision at 32 bits. A value written back at a
// width other than the one it was read at changes the declared type it stands
// for, so an operation on a shortreal shall pass 32.
Logic4Vec MakeRealVec(Arena& arena, double val, uint32_t width);

// §7.8.1/§7.8.4 — canonicalize an integral associative-array index into its
// map key. A wildcard index ([*]) is self-determined and treated as unsigned:
// leading zeros are dropped and the minimal numeric value is used, so equal
// values of differing widths collapse to one entry. A typed integral index is
// cast to its index width: sign-extended when the index type is signed and
// zero-extended when it is unsigned, which fixes the key ordering.
int64_t AssocIntKey(const Logic4Vec& val, bool is_wildcard,
                    uint32_t index_width, bool is_signed = true);

// §7.4.5/§11.5.1 — the contiguous run of positions a two-operand select
// addresses, returned as {first position, count}. Three forms share that shape
// and differ only in what the second operand means. A non-indexed part-select
// [a:b] names both endpoints, in either order, and covers them inclusively. The
// indexed forms name one endpoint and a width: [base +: w] runs upward from
// `base` and [base -: w] runs downward to it, so both cover w positions and
// only the ascending form starts at `base`. `expr` supplies which form it is
// through is_part_select_plus / is_part_select_minus; both operands are
// evaluated here, since only the width is required to be constant and the
// position may vary at run time.
//
// Positions are whatever the operands index -- bits of a vector, or elements of
// an unpacked array -- because the three forms are written and read identically
// in either case.
std::pair<uint32_t, uint32_t> SelectRange(const Expr* expr, SimContext& ctx,
                                          Arena& arena);

// §7.4.5: "A slice name of an unpacked array is an unpacked array." Appends the
// elements `expr` addresses to `out`, in ascending index order, when `expr` is
// such a slice; returns false and leaves `out` untouched when it is not, so a
// caller can fall back to reading the expression as a single value. Use this
// wherever the destination can hold an unpacked array -- a queue, another
// unpacked array -- since evaluating the slice instead yields the concatenation
// of the same elements as one packed value.
bool CollectUnpackedSliceElements(const Expr* expr, SimContext& ctx,
                                  Arena& arena, std::vector<Logic4Vec>& out);

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

// §6.19.5: every enumeration method works from "the current value of the given
// variable" and answers with a value of that variable's enumeration, so a call
// of one has to be able to find out which enumeration the variable was declared
// with. Record that for a variable created while the design runs -- one
// declared inside a procedure, or inside a function or task body. A type named
// by something other than an enumeration is left alone, so this may be called
// for any declaration whatever.
void RecordVariableEnumType(std::string_view var_name, const DataType& type,
                            SimContext& ctx);

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

// Constructs an object of `class_type`. `new_expr` is the `new` call whose
// arguments the constructor is passed, and is null for the argument-less
// `T::new` form. `loc` is where the construction was written, which a report
// about the class being abstract or an interface class names; it is separate
// from `new_expr` because that form supplies no expression to take it from.
Logic4Vec EvalClassNew(std::string_view class_type, const Expr* new_expr,
                       SimContext& ctx, Arena& arena, SourceLoc loc);

// §8.8: construct an argument-less typed constructor call `T::new` (optionally
// with parameter overrides, e.g. `E#(.N(7))::new`) used as a value expression.
// This form parses as a bare scope-resolved member access rather than a call,
// so it is not caught by the call-based class-scope dispatch; a declaration
// initializer such as `C c = D::new;` must therefore route through here to
// create an object of the specified type. Returns true (with the new object's
// handle in out) when expr is such a call.
bool TryEvalTypedConstructorNew(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out);

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
  // §21.2.1.1 / §21.2.1.7: one flag per positional value argument classifying
  // it as an unpacked aggregate: 0 = not one, 1 = one whose elements are not
  // of type byte (integer specifiers and %s reject it), 2 = an unpacked array
  // of byte (%s renders it through arg_byte_strings). A null pointer means
  // the caller supplied no type information.
  const std::vector<char>* arg_unpacked_agg = nullptr;
  // §21.2.1.7: one string per positional value argument holding the character
  // rendering of an unpacked array of byte, elements ordered from the left
  // bound of the declaration to the right bound; empty for any argument that
  // is not such an array. A null pointer means none were precomputed.
  const std::vector<std::string>* arg_byte_strings = nullptr;
  // Where the format string was written. A format specifier that cannot be
  // applied to the argument it consumes is reported here: the rendering runs
  // on values rather than on expressions, so this is the only position it can
  // name.
  SourceLoc loc;
};

// §21.2.1.5: the %m specifier prints the hierarchical name of the scope that
// invokes the display task. Rendering it requires the run-time context, so an
// optional SimContext is threaded through `opts`; when null (no simulation
// context), %m yields nothing.
std::string FormatDisplay(const std::string& fmt,
                          const std::vector<Logic4Vec>& vals,
                          const DisplayFormatOpts& opts = {});
std::string FormatArg(const Logic4Vec& val, char spec);
// §21.2.1.2: FormatArg with the automatic sizing applied to values written to
// the output -- decimal right-justified in a field sized to the largest value
// the expression's bit width admits, leading zeros replaced by spaces.
std::string FormatArgAutoSized(const Logic4Vec& val, char spec);
std::string FormatStrength(const NetStrength& ns);
std::string FormatTimeUnderTimeformat(const Logic4Vec& val,
                                      const TimeFormatSpec& spec);
std::string FormatValueAsString(const Logic4Vec& val);
std::string ExtractFormatString(const Expr* first_arg);

Logic4Vec EvalUnbasedUnsized(const Expr* expr, Arena& arena);
Logic4Vec EvalIntLiteral(const Expr* expr, Arena& arena);
Logic4Vec EvalStringLiteral(const Expr* expr, Arena& arena);

}  // namespace delta
