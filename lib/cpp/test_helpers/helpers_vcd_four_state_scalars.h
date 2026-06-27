#pragma once

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "helpers_vcd_logic4vec.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

using namespace delta;

// Registers four 1-bit signals on `vcd`, one per logic state, in the order that
// assigns identifier codes '!', '"', '#', '$':
//   z0=(0,0)->0, o1=(1,0)->1, ux=(1,1)->x, hz=(0,1)->z (canonical, Fig 38-8).
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
  unknown->value = MakeScalar(arena, 1, 1);  // x = (aval=1, bval=1)
  vcd.RegisterSignal("ux", 1, unknown);      // ident '#'
  auto* highz = arena.Create<Variable>();
  highz->value = MakeScalar(arena, 0, 1);  // z = (aval=0, bval=1)
  vcd.RegisterSignal("hz", 1, highz);      // ident '$'
}

// Writes the header, registers the four-state scalars, ends definitions, and
// dumps their values at time 0 on the already-constructed `vcd`. The caller
// owns the writer (and any mode such as SetExtended) and the enclosing scope
// that flushes it before the file is read back.
inline void WriteFourStateScalarDump(VcdWriter& vcd, Arena& arena) {
  vcd.WriteHeader("1ns");
  RegisterFourStateScalars(vcd, arena);
  vcd.EndDefinitions();
  vcd.WriteTimestamp(0);
  vcd.DumpAllValues();
}

// Asserts that a dumped VCD `content` maps each of the four logic states to its
// registration-ordered identifier code: 0->'!', 1->'"', x->'#', z->'$'.
inline void ExpectFourStateScalarChars(const std::string& content) {
  EXPECT_NE(content.find("0!"), std::string::npos);
  EXPECT_NE(content.find("1\""), std::string::npos);
  EXPECT_NE(content.find("x#"), std::string::npos);
  EXPECT_NE(content.find("z$"), std::string::npos);
}
