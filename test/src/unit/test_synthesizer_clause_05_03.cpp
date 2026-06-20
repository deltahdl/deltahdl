#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(WhiteSpaceSynthesis, VerticalTabDelimiterSynthesizes) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f, "module\vm\v;\vlogic\va\v;\vassign\va=1'b0;\vendmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(WhiteSpaceSynthesis, MixedWhitespaceSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f, "module \t\n m \f ; \v logic \t a ; assign a = 1'b0 ; endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(WhiteSpaceSynthesis, ExcessiveWhitespaceSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "   module   m   ;   logic   a   ;   assign   a   =   1'b0   ;   "
      "endmodule   ");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(WhiteSpaceSynthesis, CrlfDelimiterSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f,
                           "module m;\r\n"
                           "  logic a;\r\n"
                           "  assign a = 1'b0;\r\n"
                           "endmodule\r\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
