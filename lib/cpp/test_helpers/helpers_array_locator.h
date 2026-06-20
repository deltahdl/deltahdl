#pragma once

#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "fixture_simulator.h"

using namespace delta;

// Builds a fixed-size (non-dynamic) unpacked array as individual element
// variables named arr[i] — the representation the locator's non-queue
// collection path reads from, distinct from MakeDynArray's queue backing.
inline void MakeFixedArray(SimFixture& f, std::string_view name,
                           const std::vector<uint64_t>& vals) {
  ArrayInfo info;
  info.lo = 0;
  info.size = static_cast<uint32_t>(vals.size());
  info.elem_width = 32;
  info.is_dynamic = false;
  f.ctx.RegisterArray(name, info);
  for (size_t i = 0; i < vals.size(); ++i) {
    auto elem = std::string(name) + "[" + std::to_string(i) + "]";
    auto* v = f.ctx.CreateVariable(elem, 32);
    v->value = MakeLogic4VecVal(f.arena, 32, vals[i]);
  }
}

// Builds an integer-keyed associative array from (key, value) pairs. The keys
// need not be supplied in order; the underlying map keeps them sorted.
inline void MakeIntAssoc(SimFixture& f, std::string_view name,
                         const std::vector<std::pair<int64_t, uint64_t>>& kv,
                         uint32_t index_width = 32) {
  auto* aa = f.ctx.CreateAssocArray(
      name, /*elem_width=*/32,
      /*is_string_key=*/false,
      AssocArraySpec{index_width,
                     /*is_wildcard=*/false, /*is_4state=*/false,
                     /*is_index_signed=*/true});
  for (const auto& [k, v] : kv)
    aa->int_data[k] = MakeLogic4VecVal(f.arena, 32, v);
}
