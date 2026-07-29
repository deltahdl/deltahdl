#pragma once

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

// Decodes a packed Logic4Vec holding a SystemVerilog string (big-endian byte
// order, low byte = last character) back into a std::string.
//
// Null bytes are dropped, because a SystemVerilog string never contains one:
// §6.16 removes every "\0" as a string literal is assigned to a string
// variable. A carrier is at least one byte wide, so the empty string is stored
// as a single null byte, and keeping it would decode the empty string as a
// one-character one. This is the same rule the simulator's own decoder applies.
inline std::string VecToStr(const Logic4Vec& vec) {
  std::string result;
  uint32_t nbytes = vec.width / 8;
  for (uint32_t i = nbytes; i > 0; --i) {
    uint32_t byte_idx = i - 1;
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    auto ch = static_cast<char>((vec.words[word].aval >> bit) & 0xFF);
    if (ch != 0) result.push_back(ch);
  }
  return result;
}

// Creates a string-typed variable named `name` holding `value`, registering it
// as a string variable in the simulation context.
inline Variable* MakeStringVar(SimFixture& f, std::string_view name,
                               std::string_view value) {
  uint32_t width = static_cast<uint32_t>(value.size()) * 8;
  if (width == 0) width = 8;
  auto* var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4Vec(f.arena, width);
  for (size_t i = 0; i < value.size(); ++i) {
    auto byte_idx = static_cast<uint32_t>(value.size() - 1 - i);
    uint32_t word = (byte_idx * 8) / 64;
    uint32_t bit = (byte_idx * 8) % 64;
    var->value.words[word].aval |=
        static_cast<uint64_t>(static_cast<unsigned char>(value[i])) << bit;
  }
  f.ctx.RegisterStringVariable(name);
  return var;
}

// Elaborates and runs `src`, then checks the elements the queue `name` was
// left holding, decoded as strings, against `expected` in order.
//
// A queue whose element type is string carries its text packed into each
// element, so what a rule about building one produced is read as the sequence
// of strings rather than as the packed vectors themselves.
inline void RunAndExpectStringQueue(
    const char* src, std::string_view name,
    std::initializer_list<const char*> expected) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue(name);
  ASSERT_NE(q, nullptr);
  ASSERT_EQ(q->elements.size(), expected.size());
  size_t i = 0;
  for (const char* want : expected) {
    EXPECT_EQ(VecToStr(q->elements[i]), want) << i;
    ++i;
  }
}
