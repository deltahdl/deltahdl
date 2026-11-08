#pragma once

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/sim_context_types.h"

using namespace delta;

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
    auto* s = f.arena.AllocString(elem.c_str(), elem.size());
    auto* v = f.ctx.CreateVariable(std::string_view(s, elem.size()), 32);
    v->value = MakeLogic4VecVal(f.arena, 32, vals[i]);
  }
}

inline void MakeIntAssoc(SimFixture& f, std::string_view name,
                         const std::vector<std::pair<int64_t, uint64_t>>& kv,
                         uint32_t index_width = 32) {
  auto* aa = f.ctx.CreateAssocArray(
      name, 32, false, AssocArraySpec{index_width, false, false, true});
  for (const auto& [k, v] : kv)
    aa->int_data[k] = MakeLogic4VecVal(f.arena, 32, v);
}
