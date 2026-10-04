#pragma once

#include <cstdint>
#include <optional>
#include <string_view>

namespace delta {

// §5.12: an attribute instance as elaboration leaves it, its value folded to
// an integer or kept as the string it was written as. The RTLIR objects an
// attribute instance can be attached to each hold theirs. Moved out of
// rtlir.h, which stood at the size the assert-no-oversized-source-files job
// fails at.
struct ResolvedAttribute {
  std::string_view name;
  std::optional<int64_t> resolved_value;
  std::string_view string_value;
};

}  // namespace delta
