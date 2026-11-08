#pragma once

#include <cstdint>
#include <string>
#include <string_view>

#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

inline void SetupMem(SimFixture& f, const char* name, int lo, int size,
                     uint32_t width) {
  f.ctx.RegisterArray(
      name, {static_cast<uint32_t>(lo), static_cast<uint32_t>(size), width,
             false, false, false, true});
  for (int i = 0; i < size; ++i) {
    std::string nm = std::string(name) + "[" + std::to_string(lo + i) + "]";
    auto* s = f.arena.AllocString(nm.c_str(), nm.size());
    auto* v = f.ctx.CreateVariable(std::string_view(s, nm.size()), width);
    v->value = MakeLogic4VecVal(f.arena, width, 0);
  }
}

inline Variable* Cell(SimFixture& f, const char* name, int addr) {
  std::string nm = std::string(name) + "[" + std::to_string(addr) + "]";
  return f.ctx.FindVariable(nm);
}
