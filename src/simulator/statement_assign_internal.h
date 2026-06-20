#pragma once

#include "common/types.h"

namespace delta {

struct Expr;
class SimContext;
class Arena;

// Internal helpers shared between statement_assign_core.cpp,
// statement_assign_stream.cpp, and statement_assign_decl.cpp. Each symbol is
// defined in exactly one of those translation units.

// Defined in statement_assign_core.cpp.
void CoerceTo2State(Logic4Vec& v);

// Defined in statement_assign_stream.cpp.
void UnpackStreamingConcatLhs(const Expr* lhs, const Logic4Vec& rhs_val,
                              SimContext& ctx, Arena& arena);

}  // namespace delta
