#pragma once

#include <cstdint>
#include <string_view>

#include "elaborator/rtlir.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

// Readings of one parameter of module m in an elaborated design, shared by
// the test_elaborator_subclause_20_06_02 family so that each file states the
// parameter it reads and not the walk to it.

// The resolved value of parameter `name` of module m, or -1 where the module
// declares none or the fold left it unresolved: no test expects -1 of a
// parameter it reads, so the two failures read as one wrong number.
inline int64_t ParamValue(RtlirDesign* design, std::string_view name) {
  const auto* p = FindParam(design, "m", name);
  return p != nullptr && p->is_resolved ? p->resolved_value : -1;
}

// Whether the fold left parameter `name` of module m without a value.
inline bool ParamUnresolved(RtlirDesign* design, std::string_view name) {
  const auto* p = FindParam(design, "m", name);
  return p == nullptr || !p->is_resolved;
}
