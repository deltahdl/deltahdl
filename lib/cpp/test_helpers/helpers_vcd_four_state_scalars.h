#pragma once

#include "common/arena.h"
#include "helpers_vcd_logic4vec.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

using namespace delta;

// Registers four 1-bit signals on `vcd`, one per logic state, in the order that
// assigns identifier codes '!', '"', '#', '$':
//   z0=(0,0)->0, o1=(1,0)->1, ux=(0,1)->x, hz=(1,1)->z.
// Callers invoke this between WriteHeader and EndDefinitions, then dump values
// and assert each state maps to its binary value character.
inline void RegisterFourStateScalars(VcdWriter& vcd, Arena& arena) {
  auto* zero = arena.Create<Variable>();
  zero->value = MakeScalar(arena, 0, 0);
  vcd.RegisterSignal("z0", 1, zero);  // ident '!'
  auto* one = arena.Create<Variable>();
  one->value = MakeScalar(arena, 1, 0);
  vcd.RegisterSignal("o1", 1, one);  // ident '"'
  auto* unknown = arena.Create<Variable>();
  unknown->value = MakeScalar(arena, 0, 1);
  vcd.RegisterSignal("ux", 1, unknown);  // ident '#'
  auto* highz = arena.Create<Variable>();
  highz->value = MakeScalar(arena, 1, 1);
  vcd.RegisterSignal("hz", 1, highz);  // ident '$'
}
