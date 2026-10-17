#pragma once

#include <cstdint>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/source_loc.h"

namespace delta {

struct Expr;

// §5.12: an attribute instance as elaboration leaves it, its value folded to
// an integer or kept as the string it was written as. The RTLIR objects an
// attribute instance can be attached to each hold theirs. Moved out of
// rtlir.h, which stood at the size the assert-no-oversized-source-files job
// fails at.
struct ResolvedAttribute {
  std::string_view name;
  std::optional<int64_t> resolved_value;
  std::string_view string_value;
  // §37.83: the expression the value was written as, null where none was,
  // and where the attribute instance was written, which an attribute object
  // reports its value and definition location from.
  const Expr* value = nullptr;
  SourceLoc loc;
};

// §37.83 with §5.12: the attribute instances elaboration resolved on the
// syntax nodes of a module instance, or of the classes outside every module,
// that keep no record of their own -- a task or function, a gate or UDP
// instance, a specparam, a concurrent assertion, a sequence or property
// declaration, a clocking block, a statement, an operator, a class and a class
// item -- keyed by the node, from which the VPI object made of the node takes
// its attributes.
using RtlirNodeAttributes =
    std::unordered_map<const void*, std::vector<ResolvedAttribute>>;

}  // namespace delta
