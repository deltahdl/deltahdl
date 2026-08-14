#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_synthesizer.h"
#include "helpers_aig_eval.h"
#include "synthesizer/synth_lower.h"

// What a module computes from one input word, for the unit files whose cases
// drive a single wide input port. Every case hands the netlist the values 0 to
// `values - 1` and expects the output word to carry `expected(v)`.

// Drive the values 0 to `values - 1` through the netlist `src` lowers to, and
// expect the output word to carry `expected(v)`. `SynthLower::MapPorts` at
// src/synthesizer/synth_lower.cpp:261 walks `mod->ports` in declaration order
// and allocates one AIG input per bit, low bit first, so bit i of the driven
// word is bit i of the module's input storage.
// `SynthLower::RegisterOutputs` at src/synthesizer/synth_lower.cpp:756 emits
// each output port's bits the same way, so bit j of the word `EvalAigOutputs`
// answers is bit j of the module's output storage.
//
// `ExpectAssignSweep` in lib/cpp/test_helpers/helpers_synth_assign.h drives a
// fixed four-bit `a` against a second operand. This one drives a single word,
// which is what a case over one wide input port needs.
//
// The netlist is driven rather than checked for being non-null because
// `ASSERT_NE(aig, nullptr)` and `EXPECT_FALSE(f.diag.HasErrors())` both hold
// over a netlist whose every output bit is constant zero, which is what a
// missing lowering produces.
inline void ExpectInputSweep(const std::string& src, uint64_t values,
                             uint64_t (*expected)(uint64_t)) {
  SCOPED_TRACE(src);
  SynthFixture f;
  const auto* mod = ElaborateSrc(f, src);
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  const auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  for (uint64_t v = 0; v < values; ++v) {
    EXPECT_EQ(EvalAigOutputs(*aig, v), expected(v)) << "input = " << v;
  }
}
