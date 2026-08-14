#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_synthesizer.h"
#include "helpers_aig_eval.h"
#include "synthesizer/synth_lower.h"

// Expect `src` to lower to a netlist whose one output carries `a` where the
// two-bit `sel` is 0, `b` where it is 1 and `c` at the two values left, over a
// module declaring `input [1:0] sel, input a, input b, input c` and one output.
// The three spellings of that selection -- a chained conditional expression, an
// if-else-if chain, and the same chain written `unique` -- are covered in
// separate files, and each drives the netlist here.
//
// The sweep fails on the netlist those modules lowered to before `sel == 2'd0`
// and `sel == 2'd1` had a lowering: both comparisons answered
// `AigGraph::kConstFalse`, and `AigGraph::AddMux` with a constant-false select
// hands back the else literal and builds no node, so the output carried `c` for
// every value of `sel` while `a` and `b` reached nothing. An output count never
// notices that, because the port list fixes the count whatever the netlist
// computes.
//
// `SynthLower::MapPorts` walks `mod->ports` in declaration order and allocates
// one AIG input per bit, low bit first, so bit 0 of the word handed to
// `EvalAigOutputs` is sel[0], bit 1 is sel[1], bit 2 is `a`, bit 3 is `b` and
// bit 4 is `c`. Each value of `sel` is driven against all eight combinations of
// the three data inputs, because a netlist reading the wrong source agrees with
// the right one wherever the two sources happen to carry the same value.
inline void ExpectSelChoosesAmongThreeSources(const std::string& src) {
  SCOPED_TRACE(src);
  SynthFixture f;
  const auto* mod = ElaborateSrc(f, src);
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  const auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
  EXPECT_EQ(aig->outputs.size(), 1);
  for (uint64_t sel = 0; sel < 4; ++sel) {
    for (uint64_t data = 0; data < 8; ++data) {
      uint64_t a = data & 1U;
      uint64_t b = (data >> 1) & 1U;
      uint64_t c = (data >> 2) & 1U;
      uint64_t expected = sel == 0 ? a : (sel == 1 ? b : c);
      EXPECT_EQ(EvalAigOutputs(*aig, sel | (data << 2)), expected)
          << "sel = " << sel << ", a = " << a << ", b = " << b << ", c = " << c;
    }
  }
}
