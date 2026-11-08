#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_synthesizer.h"
#include "helpers_aig_eval.h"
#include "synthesizer/synth_lower.h"

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
