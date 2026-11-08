#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_synthesizer.h"
#include "helpers_aig_eval.h"
#include "synthesizer/synth_lower.h"

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
