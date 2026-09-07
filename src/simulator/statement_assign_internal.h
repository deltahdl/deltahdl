#pragma once

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/types.h"

namespace delta {

struct ArrayInfo;
struct Expr;
struct Stmt;
class SimContext;
class Arena;
enum class DataTypeKind : uint8_t;

// Internal helpers shared across the statement_assign_*.cpp family and the
// handful of other translation units that reach into it. Each symbol is
// defined in exactly one translation unit, which that symbol's own comment
// names.

// Defined in statement_assign_core.cpp.
void CoerceTo2State(Logic4Vec& v);

// Defined in statement_assign_core.cpp; also used by the §11.4.2 nonblocking
// path in statement_assign_nonblocking.cpp and by the subroutine-body statement
// executor in eval_function_body.cpp, which applies §10.7 to its own writes.
// Convert the rhs value when the lhs and rhs differ in real-ness or real width
// before a write.
Logic4Vec ConvertRealOnAssign(Logic4Vec rhs_val, const Expr* lhs,
                              uint32_t target_width, SimContext& ctx,
                              Arena& arena);

// Defined in statement_assign_core.cpp; also used by lowerer_var.cpp for the
// declaration-initializer form of the §6.12.1 conversion. Same rule as
// ConvertRealOnAssign but with the lhs real-ness supplied directly, for callers
// that have no lhs Expr (e.g. a variable declared with an initializer).
Logic4Vec ConvertRealForKnownLhs(Logic4Vec rhs_val, bool lhs_is_real,
                                 uint32_t target_width, Arena& arena);

// Defined in statement_assign_core.cpp; also used by the subroutine-body
// statement executor in eval_function_body.cpp. §11.4.1 states a compound
// assignment as one blocking assignment -- "an assignment operator is
// semantically equivalent to a blocking assignment, with the exception that any
// left-hand index expression is only evaluated once" -- and this performs that
// one read-modify-write for whichever of the identifier, select, member-access
// and scalar-fallback forms the target takes. A caller that reaches it has had
// its statement written for it and must not go on to write the target again
// from the value of stmt->rhs, which is the compound operator over the same lhs
// node and would assign it a second time.

void ApplyCompoundAssignOp(const Stmt* stmt, SimContext& ctx, Arena& arena);

// Defined in statement_assign_core.cpp; also used by EvalCompoundAssign in
// eval_expr.cpp. §11.4.1 makes one exception to a compound assignment being an
// ordinary blocking assignment -- "any left-hand index expression is only
// evaluated once" -- and the helpers that resolve, read and write a select
// target each re-derive it from lhs->index, which would call a side-effecting
// index several times. Snapshot evaluates each index node once and stashes the
// result for those later reads to find; Clear undoes it, and has to run on
// every exit or the snapshot leaks into a later statement reusing the same
// node.
void SnapshotSelectIndices(const Expr* lhs, SimContext& ctx, Arena& arena);
void ClearSelectIndices(const Expr* lhs, SimContext& ctx);

// Defined in statement_assign_core.cpp; also used by the subroutine-body
// statement executor in eval_function_body.cpp. §10.4 lists "Bit-selects,
// part-selects, and slices of packed arrays" among the left-hand sides a
// procedural assignment may take, alongside the elements of the arrays of
// Clause 7, and this decides which of those a select names and writes it
// accordingly. Always returns true: a select target is this function's to
// answer for, whether or not it found something to write.
bool TrySelectBlockingAssign(const Expr* lhs, Logic4Vec& rhs_val,
                             SimContext& ctx, Arena& arena);

// Defined in statement_assign_core.cpp; also used by the subroutine-body
// statement executor in eval_function_body.cpp. §10.4 puts procedural
// assignments "within procedures such as always, initial, task, and function",
// so a concatenation or assignment-pattern target is written the same way in a
// subroutine body as outside one. Returns false when the lhs is neither, so the
// caller goes on to its other forms.
bool TryUnpackConcatLhs(const Expr* lhs, const Logic4Vec& rhs_val,
                        SimContext& ctx, Arena& arena);

// Defined in statement_assign_core.cpp; also used by the subroutine-body
// statement executor in eval_function_body.cpp. §10.7: "The size of the
// left-hand side of an assignment forms the context for the right-hand
// expression", and §11.6.1 makes that context part of what sizes the
// expression. The width of the object the lhs names, or the sum of a
// concatenation's element widths; 0 where the lhs names nothing this can
// resolve, which EvalExpr reads as self-determined.
uint32_t LhsContextWidth(const Expr* lhs, SimContext& ctx);

// Defined in statement_assign_core.cpp; also used by the §11.4.2 nonblocking
// path in statement_assign_nonblocking.cpp. Evaluate the rhs with the lhs as
// the assignment context (width and, for named patterns, struct type).
Logic4Vec EvalRhsWithStructContext(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena);

// Defined in statement_assign_stream.cpp; also used by the §11.4.2 nonblocking
// path in statement_assign_nonblocking.cpp. §11.4.14: left-align a streaming
// concatenation source in a wider fixed-size target.
Logic4Vec ApplyStreamPackToTargetWidening(const Stmt* stmt, Logic4Vec rhs_val,
                                          SimContext& ctx, Arena& arena);

// Defined in statement_assign_stream.cpp.
void UnpackStreamingConcatLhs(const Expr* lhs, const Logic4Vec& rhs_val,
                              SimContext& ctx, Arena& arena);

// Defined in statement_assign_stream.cpp; also used by the blocking-assignment
// dispatch in statement_assign_core.cpp, which offers a statement to it before
// falling through to the generic write. §11.4.14: a streaming concatenation
// assigned to a dynamically sized target left-aligns in that target, so the
// queue is resized to the smallest number of elements at least as wide as the
// stream and the stream is padded with zero bits on the right before being
// carved into them. Returns false, having written nothing, when the right-hand
// side is not a streaming concatenation, the left-hand side does not name a
// queue, or the queue's element width is unknown; the caller then goes on to
// its other forms.
bool TryStreamingConcatToQueueTarget(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena);

// Geometry of an array/queue target addressed by a `with` clause (§11.4.14.3):
// `size` is the element count and `lo` is the declared low index.
struct ArrayGeom {
  uint32_t size;
  uint32_t lo;
};

// Half-open slice window [start, start + count) selected by a `with` clause.
struct StreamSliceRange {
  uint32_t start;
  uint32_t count;
};

// Resolves an optional `with` range expression on an array target into a
// 0-based [out_range.start, out_range.start + out_range.count) window. Returns
// false when an explicit single-index selection lands out of bounds. Defined in
// statement_assign_stream.cpp; also used by eval_streaming.cpp.
bool ResolveWithRange(const Expr* with_expr, SimContext& ctx, Arena& arena,
                      ArrayGeom geom, StreamSliceRange& out_range);

// Assignment-pattern key helpers, defined in statement_assign_pattern.cpp;
// also used by lowerer_var.cpp. IsTypeKeyword recognizes a type-name pattern
// key; TypeKeyMatchesKind tests whether such a key selects the given element
// kind.
bool IsTypeKeyword(std::string_view key);
bool TypeKeyMatchesKind(std::string_view key, DataTypeKind kind);

// Defined in statement_assign_pattern.cpp.
// §10.9: the index an array pattern key names. Syntax 10-5 writes such a key as
// a constant expression -- `array_pattern_key ::= constant_expression` -- so
// the index is what the whole expression evaluates to, not what the text of its
// first token reads as: `8'd3` names element 3, and `N-1` names one element as
// definitely as a bare number does. `default` and a simple-type key name no
// index and are not asked about here.
uint32_t PatternKeyIndex(const Expr* key, SimContext& ctx, Arena& arena);

// §7.10.4: the elements a right-hand side contributes to a queue it is
// assigned to. An item naming a queue or an unpacked array contributes that
// object's elements, a queue slice contributes the run of elements it names,
// and anything else contributes the one value it evaluates to. A right-hand
// side that is not a concatenation is itself the single item, which is what
// makes `q = q[1:$]` a queue of the elements the slice names rather than a
// queue holding one value.
//
// Every element is copied into `out` before any caller writes it back, so a
// right-hand side reading the queue it is assigned to is safe.
//
// Defined in statement_assign_pattern.cpp; also used by the nonblocking form of
// the same assignment in statement_assign_nonblocking.cpp.
void CollectQueueElements(const Expr* expr, SimContext& ctx, Arena& arena,
                          std::vector<Logic4Vec>& out);

// Defined in statement_assign.cpp; also used by the array-copy form of a
// pattern assignment in statement_assign_pattern.cpp. Copies element by
// element over the overlap of the two arrays, leaving any excess destination
// element untouched.
void CopyArrayElements(std::string_view dst_name, const ArrayInfo& dst,
                       std::string_view src_name, const ArrayInfo& src,
                       SimContext& ctx);

}  // namespace delta
