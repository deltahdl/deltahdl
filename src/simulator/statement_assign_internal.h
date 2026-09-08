#pragma once

#include <cstdint>
#include <string_view>
#include <vector>

#include "common/packed_range.h"
#include "common/types.h"

namespace delta {

struct ArrayInfo;
struct Expr;
struct Stmt;
struct Variable;
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

// Defined in statement_assign_core.cpp; also used by the nonblocking scheduler
// in statement_assign_nonblocking.cpp, which needs the answer before it takes
// an event from the pool rather than after. §11.4.12 gives a concatenation the
// left-hand side of an assignment and §10.9 gives an assignment pattern, bare
// or typed, the same use, so the three are one kind of target. Answers whether
// the left-hand side is one of them, a typed pattern's cast looked through.
bool IsConcatLhs(const Expr* lhs);

// Defined in statement_assign_core.cpp; also used by the §10.6.1 and §10.6.2
// procedural continuous assignments in statement_assign_decl.cpp, whose
// concatenation targets walk the same elements. §10.9 lets an assignment
// pattern carry a type prefix -- `type_reference '{...}` -- and that prefix is
// a cast around the pattern rather than a target of its own, so a caller that
// means to walk the pattern's elements has to look through it first. Answers
// the pattern a typed pattern wraps, and the expression itself otherwise.
const Expr* UnwrapTypedPattern(const Expr* expr);

// Defined in statement_assign_core.cpp; also used by the §11.4.14 streaming
// unpack in statement_assign_stream.cpp, which sizes a target element that is a
// select with it. §11.5.1: how wide the select `sel` on `var` is as an
// expression -- one bit for an ordinary bit-select, the element width for the
// index of a packed multidimensional array (§7.4.1), and the span of the
// indices for a part-select, indexed or not. An address outside the declared
// bounds changes none of those: §11.5.1 gives the invalid reference a value
// rather than an absence, "x for 4-state and 0 for 2-state values", and says
// separately that such a write "shall have no effect on the data stored". Zero
// only where the select names no bits, which is a part-select whose bounds or
// width expression carry x or z and an indexed one whose width is zero,
// §11.5.1 requiring that width to "be a positive constant".
//
// This is the width the select names and not the window of its object it may
// write; the second question is SelectStorageBits'. The two differ wherever a
// select runs off the end of its object, and a caller that asked one of them
// for both drew its element boundaries in the wrong place.
uint32_t SelectExprWidth(const Variable& var, const Expr* sel, SimContext& ctx,
                         Arena& arena);

// Defined in statement_assign_core.cpp; also used by the §10.6.1 and §10.6.2
// procedural continuous assignments in statement_assign_decl.cpp, which cut a
// forced or assigned value into the same element windows a blocking assignment
// cuts it into. §11.4.12/§11.5.1: the width of one concatenation lvalue element
// -- a nested concatenation or assignment pattern sums its own elements, a
// select is as wide as the bits §11.5.1 gives its indices whether or not they
// are in bounds, and any other form is as wide as the variable it resolves to.
// Zero for an element this cannot size at all, which a caller passes over
// without advancing its offset.
//
// This is the element's width as an expression and not the window of its object
// it may write; the second question is ConcatLhsElemHasWritableBits' and
// SelectStorageBits'. Answering the window to both dropped an element
// addressing no bit out of the concatenation entirely, and every element to its
// left then took its bits one element too low.
uint32_t ConcatLhsElemWidth(const Expr* e, SimContext& ctx, Arena& arena);

// Defined in statement_assign_core.cpp; also used by the §10.6.1 and §10.6.2
// procedural continuous assignments in statement_assign_decl.cpp, which have
// the same element to decline. §11.5.1: whether the concatenation lvalue
// element `e`, having resolved to `var`, addresses any bit of it -- false for
// the select whose address lies wholly outside the declared bounds or carries x
// or z, whose write "shall have no effect on the data stored", and true for
// every other element shape, each of which names its whole variable. An element
// this answers false for still occupies ConcatLhsElemWidth's bits of the value.
bool ConcatLhsElemHasWritableBits(const Expr* e, const Variable& var,
                                  SimContext& ctx, Arena& arena);

// Defined in statement_assign.cpp, whose bit-select writer raises it before it
// resolves a window; also used by the §11.4.12 concatenation unpack in
// statement_assign_core.cpp and by the §10.6.1 and §10.6.2 procedural
// continuous assignments in statement_assign_decl.cpp, each of which sizes a
// concatenation element itself and so never reaches that writer with one this
// concerns. §11.5.1 requires an indexed part-select's width to "be a positive
// constant", which makes a zero-width one illegal rather than merely empty,
// and this raises that error for the select `sel`. It asks the question of the
// select as written: it returns silently unless `sel` has an index_end, is a
// plus or minus indexed part-select, and reads a declared width of zero, so a
// caller may offer it every element it passed over and the ones whose width is
// zero for another reason -- an element nothing here can size, bounds carrying
// x or z -- stay as silent as they were. Reporting is all it does; the caller
// still passes the element over without advancing its offset.
void ReportZeroWidthPartSelect(const Expr* sel, SimContext& ctx, Arena& arena);

// Defined in statement_assign_core.cpp; also used by the subroutine-body
// statement executor in eval_function_body.cpp. §10.4 puts procedural
// assignments "within procedures such as always, initial, task, and function",
// so a concatenation or assignment-pattern target is written the same way in a
// subroutine body as outside one. Returns false when the lhs is neither, so the
// caller goes on to its other forms.
bool TryUnpackConcatLhs(const Expr* lhs, const Logic4Vec& rhs_val,
                        SimContext& ctx, Arena& arena);

// Defined in statement_assign_core.cpp; also used by the subroutine-body
// statement executor in eval_function_body.cpp, the §11.4.1 compound
// assignment in eval_expr_assign_ops.cpp and the §10.6 procedural continuous
// assignments in statement_assign_decl.cpp. §10.7: "The size of the left-hand
// side of an assignment forms the context for the right-hand expression", and
// §11.6.1 makes that context part of what sizes the expression. The width of
// the object the lhs names, the bits §11.5.1 gives a select's indices, or the
// sum of a concatenation's or assignment pattern's element widths -- the same
// question ConcatLhsElemWidth answers of one element, asked of the whole lhs,
// and answered by it. 0 where the lhs names no bits at all, either because
// nothing here can resolve it or because it is a zero-width part-select, which
// EvalExpr reads as self-determined.
uint32_t LhsContextWidth(const Expr* lhs, SimContext& ctx, Arena& arena);

// Defined in statement_assign_core.cpp; also used by the §11.4.2 nonblocking
// path in statement_assign_nonblocking.cpp. Evaluate the rhs with the lhs as
// the assignment context (width and, for named patterns, struct type).
Logic4Vec EvalRhsWithStructContext(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena);

// The whole-object assignment forms, defined in statement_assign_object.cpp
// and each used by the blocking-assignment dispatch in
// statement_assign_core.cpp, which offers a statement to them in turn before
// evaluating any right-hand value. None of them sizes its right-hand side
// against the width of its target, because neither an associative array nor a
// class handle takes a value the way §10.7 sizes one for a vector; each
// answers the statement whole or declines it, returning false having written
// nothing, and the caller then goes on to its other forms.
//
// §7.9.11 lets a whole associative array be written at once. Copy takes the
// entries of another associative array named on the right; Map takes those
// §7.12.5's map() produced, whose set of index values matches its source with
// each stored value replaced by the value of the with expression; Literal
// takes them from an '{index:value} assignment pattern, reading each key as an
// index of the array's declared index type and `default` as the array's
// default. All three replace the destination's previous contents rather than
// merging into them.
bool TryAssocCopyAssign(const Stmt* stmt, SimContext& ctx);
bool TryAssocMapAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);
bool TryAssocLiteralAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

// §8.3's class `new` in the two forms whose type comes from somewhere other
// than the target's own declared class. Typed is the class-scope call
// `obj = C::new`, which names the type on the right and binds §8.25's
// specialization overrides as locals around the construction when the scope is
// parameterized; Member is `obj.field = new`, whose bare `new` carries no type
// at all, so the field's declared class is resolved from the class type of the
// base and the resulting handle stored through the member chain. The form
// whose type is the target's, `obj = new`, is TryClassNewAssign, which
// simulator/statement_assign.h declares.
bool TryTypedClassNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);
bool TryMemberClassNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

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

// Defined in statement_assign.cpp; also used by the §11.4.2 nonblocking path in
// statement_assign_nonblocking.cpp, whose deferred update deposits the window
// its own left-hand side named. §11.5.1 has a part-select that is only partly
// in range "when written, only affect the bits that are in range", and this
// writes `rhs_val` into exactly the window `bits` names: `bits.lo` and
// `bits.width` are the bits of `var` that are affected, and `bits.src_lo` is
// where in the value the bits they receive begin. `bits` is what
// SelectStorageBits (statement_assign.h) answers, and the two are meant to be
// asked in that order, so that one statement of the clause resolves a select
// and one deposits it.
//
// The deposit is made bit by bit and not in a machine word: a target wider
// than 64 bits keeps the bits above the first word, the x and z §6.3.1 lets a
// 4-state bit hold survive the round trip, and a window beginning at bit 64 or
// above lands where it was named. The definition's own comment gives the three
// wrong answers that says.
//
// A forced target is the caller's to decline, because the two callers ask at
// different moments. §10.6.2 has a force override a procedural assignment
// "until a release procedural statement is executed on the variable"; the
// blocking caller WriteBitSelect asks before it evaluates the indices, while
// the nonblocking one has to ask inside its update callback, the flag that
// governs the write being the one standing when the update region runs rather
// than when the event was queued.
void WritePartSelect(Variable* var, const PartSelectBits& bits,
                     const Logic4Vec& rhs_val, Arena& arena);

// Defined in statement_assign.cpp; also used by the array-copy form of a
// pattern assignment in statement_assign_pattern.cpp. Copies element by
// element over the overlap of the two arrays, leaving any excess destination
// element untouched.
void CopyArrayElements(std::string_view dst_name, const ArrayInfo& dst,
                       std::string_view src_name, const ArrayInfo& src,
                       SimContext& ctx);

}  // namespace delta
