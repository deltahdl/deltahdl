#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_synthesizer.h"
#include "helpers_aig_eval.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

// What a §11.4 operator lowers to, for the unit files that cover one operator
// subclause each. Every case in those files drives one continuous assignment
// through the synthesizer and reads the netlist back, so the module source, the
// sweep and the rejection are stated here once rather than in each file.

// The source of a module whose continuous assignment drives the four-bit output
// `y` from `rhs`, over the input ports `inputs` declares. The whole assignment
// is on line 2, which is the line a report about it stands at.
//
// `y` is four bits wide so that a case can say which bit of the target carries
// the result. §11.4.4, §11.4.5 and §11.4.6 make a comparison one bit wide, and
// a lowering answering it at every bit index drives `y` to 15 where those
// subclauses ask for 1.
inline std::string ModuleAssigning(std::string_view inputs,
                                   std::string_view rhs) {
  return std::string("module m(") + std::string(inputs) +
         ", output logic [3:0] y);\n  assign y = " + std::string(rhs) +
         ";\nendmodule\n";
}

// Drive every four-bit value of `a` against `b_values` values of `b` through
// the netlist `src` lowers to, and expect the output word to carry
// `expected(a, b)`. `SynthLower::MapPorts` walks `mod->ports` in declaration
// order and allocates one AIG input per bit, so `a` takes bits 0 to 3 of the
// word handed to `EvalAigOutputs` and `b` starts at bit 4. A module declaring
// one input is swept with `b_values` of 1.
//
// `ASSERT_NE(aig, nullptr)` and `EXPECT_FALSE(f.diag.HasErrors())` both hold
// over a netlist whose every output bit is constant zero, so the sweep is what
// states which function of the operands the netlist computes. Every
// combination is driven rather than one pair, because a netlist computing some
// other function is free to agree at the pair chosen: a chain wired wrongly
// above its low bits agrees wherever those bits decide the answer.
//
// The whole output word is compared rather than its low bit, so a lowering
// answering a one-bit result at every bit index of `y` fails here as well.
inline void ExpectAssignSweep(const std::string& src, uint64_t b_values,
                              uint64_t (*expected)(uint64_t, uint64_t)) {
  SCOPED_TRACE(src);
  SynthFixture f;
  const auto* mod = ElaborateSrc(f, src);
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  const auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  for (uint64_t a = 0; a < 16; ++a) {
    for (uint64_t b = 0; b < b_values; ++b) {
      EXPECT_EQ(EvalAigOutputs(*aig, a | (b << 4)), expected(a, b))
          << "a = " << a << ", b = " << b;
    }
  }
}

// Expect the module assigning `rhs` over the ports `inputs` declares to be
// refused rather than lowered, with the error containing `message` standing at
// line 2 under `subclause`. `SynthLower::Lower` answering a graph is the
// failure this guards against, because that graph carries an output the design
// never asked for and nothing tells the reader an operator was dropped.
inline void ExpectAssignReported(std::string_view inputs, std::string_view rhs,
                                 std::string_view message,
                                 std::string_view subclause) {
  SCOPED_TRACE(std::string(rhs));
  SynthFixture f;
  const auto* mod = ElaborateSrc(f, ModuleAssigning(inputs, rhs));
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  EXPECT_EQ(synth.Lower(mod), nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, 2, subclause));
}
