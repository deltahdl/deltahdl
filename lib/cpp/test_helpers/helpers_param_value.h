#pragma once

#include <cstdint>
#include <string_view>

#include "elaborator/rtlir.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

inline int64_t ParamValue(RtlirDesign* design, std::string_view name) {
  const auto* p = FindParam(design, "m", name);
  return p != nullptr && p->is_resolved ? p->resolved_value : -1;
}

inline bool ParamUnresolved(RtlirDesign* design, std::string_view name) {
  const auto* p = FindParam(design, "m", name);
  return p == nullptr || !p->is_resolved;
}
