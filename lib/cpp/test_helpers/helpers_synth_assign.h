#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "fixture_synthesizer.h"
#include "helpers_aig_eval.h"
#include "helpers_reported_error.h"
#include "synthesizer/synth_lower.h"

inline std::string ModuleAssigningTo(std::string_view target,
                                     std::string_view inputs,
                                     std::string_view rhs) {
  return std::string("module m(") + std::string(inputs) + ", " +
         std::string(target) + ");\n  assign y = " + std::string(rhs) +
         ";\nendmodule\n";
}

inline std::string ModuleAssigning(std::string_view inputs,
                                   std::string_view rhs) {
  return ModuleAssigningTo("output logic [3:0] y", inputs, rhs);
}

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
