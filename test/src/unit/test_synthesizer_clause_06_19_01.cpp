#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(TypedefEnumSynthesis, NamedEnumTypeSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  typedef enum {NO, YES} boolean;\n"
      "  boolean flag;\n"
      "  assign flag = YES;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(TypedefEnumSynthesis, NamedEnumTypeReusedForMultipleVars) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  typedef enum {OFF, ON} switch_t;\n"
      "  switch_t a;\n"
      "  switch_t b;\n"
      "  assign a = OFF;\n"
      "  assign b = ON;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
