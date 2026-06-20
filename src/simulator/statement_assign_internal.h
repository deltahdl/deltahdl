#pragma once

#include <cstdint>
#include <string_view>

#include "common/types.h"

namespace delta {

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

// Resolves an optional `with` range expression on an array target into a
// 0-based [out_start, out_start + out_count) window. Returns false when an
// explicit single-index selection lands out of bounds. Defined in
// statement_assign_stream.cpp; also used by eval_streaming.cpp.
bool ResolveWithRange(const Expr* with_expr, SimContext& ctx, Arena& arena,
                      uint32_t array_size, uint32_t array_lo,
                      uint32_t& out_start, uint32_t& out_count);

// Assignment-pattern key helpers (defined in statement_assign.cpp; also used by
// lowerer_var.cpp). IsTypeKeyword recognizes a type-name pattern key;
// TypeKeyMatchesKind tests whether such a key selects the given element kind.
bool IsTypeKeyword(std::string_view key);
bool TypeKeyMatchesKind(std::string_view key, DataTypeKind kind);

}  // namespace delta
