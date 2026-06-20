#pragma once

#include <cstdint>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

// Returns true when net `name` has settled to the known scalar value `expected`
// (aval matches the low bit of expected, bval clear).
inline bool SettledToKnown(SimFixture& f, std::string_view name,
                           uint64_t expected) {
  auto* v = f.ctx.FindVariable(name);
  if (!v) return false;
  return (v->value.words[0].aval & 1u) == (expected & 1u) &&
         (v->value.words[0].bval & 1u) == 0u;
}

// Returns true when net `name` has settled to high-impedance (aval clear,
// bval set on the low bit).
inline bool SettledToHighZ(SimFixture& f, std::string_view name) {
  auto* v = f.ctx.FindVariable(name);
  if (!v) return false;
  return (v->value.words[0].aval & 1u) == 0u &&
         (v->value.words[0].bval & 1u) == 1u;
}
