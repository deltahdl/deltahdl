#pragma once

#include <cstdint>
#include <string>
#include <string_view>

namespace delta {

class SimContext;

// Internal helper shared between eval_expr.cpp and eval_streaming.cpp. Defined
// in eval_expr.cpp. Resolves a type name (built-in or user-defined) to its bit
// width, defaulting to 32 for unknown names.
uint32_t ResolveCastWidth(std::string_view type_name, SimContext& ctx);

// Strips a leading "$root.<top>." prefix from a hierarchical name, returning
// the remainder; names without the prefix are returned unchanged. Defined in
// eval_expr.cpp; also used by statement_assign.cpp.
std::string StripRootPrefix(const std::string& name);

}  // namespace delta
