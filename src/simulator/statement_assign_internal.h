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

// Internal helpers shared between statement_assign_core.cpp,
// statement_assign_stream.cpp, and statement_assign_decl.cpp. Each symbol is
// defined in exactly one of those translation units.

// Defined in statement_assign_core.cpp.
void CoerceTo2State(Logic4Vec& v);

// Defined in statement_assign_core.cpp; also used by the §11.4.2 nonblocking
// path in statement_assign_nonblocking.cpp. Convert the rhs value when the lhs
// and rhs differ in real-ness or real width before a write.
Logic4Vec ConvertRealOnAssign(Logic4Vec rhs_val, const Expr* lhs,
                              uint32_t target_width, SimContext& ctx,
                              Arena& arena);

// Defined in statement_assign_core.cpp; also used by lowerer_var.cpp for the
// declaration-initializer form of the §6.12.1 conversion. Same rule as
// ConvertRealOnAssign but with the lhs real-ness supplied directly, for callers
// that have no lhs Expr (e.g. a variable declared with an initializer).
Logic4Vec ConvertRealForKnownLhs(Logic4Vec rhs_val, bool lhs_is_real,
                                 uint32_t target_width, Arena& arena);

// Defined in statement_assign_core.cpp; also used by the §11.4.2 nonblocking
// path in statement_assign_nonblocking.cpp. Evaluate the rhs with the lhs as
// the assignment context (width and, for named patterns, struct type).
Logic4Vec EvalRhsWithStructContext(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena);

// Defined in statement_assign_core.cpp; also used by the §11.4.2 nonblocking
// path in statement_assign_nonblocking.cpp. §11.4.14: left-align a streaming
// concatenation source in a wider fixed-size target.
Logic4Vec ApplyStreamPackToTargetWidening(const Stmt* stmt, Logic4Vec rhs_val,
                                          SimContext& ctx, Arena& arena);

// Defined in statement_assign_stream.cpp.
void UnpackStreamingConcatLhs(const Expr* lhs, const Logic4Vec& rhs_val,
                              SimContext& ctx, Arena& arena);

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

// Assignment-pattern key helpers (defined in statement_assign.cpp; also used by
// lowerer_var.cpp). IsTypeKeyword recognizes a type-name pattern key;
// TypeKeyMatchesKind tests whether such a key selects the given element kind.
bool IsTypeKeyword(std::string_view key);
bool TypeKeyMatchesKind(std::string_view key, DataTypeKind kind);

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
