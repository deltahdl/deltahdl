#pragma once

#include <cstdint>
#include <string_view>

namespace delta {

class SimContext;

// Internal helper shared between eval_expr.cpp and eval_streaming.cpp. Defined
// in eval_expr.cpp. Resolves a type name (built-in or user-defined) to its bit
// width, defaulting to 32 for unknown names.
uint32_t ResolveCastWidth(std::string_view type_name, SimContext& ctx);

}  // namespace delta
