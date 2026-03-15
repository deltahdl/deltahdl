#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(WhiteSpaceSynthesis, SpaceDelimiterSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f, "module m; logic a; assign a = 1'b0; endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(WhiteSpaceSynthesis, TabDelimiterSynthesizes) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f, "module\tm;\tlogic\ta;\tassign\ta=1'b0;\tendmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(WhiteSpaceSynthesis, NewlineDelimiterSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f, "module\nm\n;\nlogic\na\n;\nassign\na\n=\n1'b0\n;\nendmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(WhiteSpaceSynthesis, FormfeedDelimiterSynthesizes) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f, "module\fm\f;\flogic\fa\f;\fassign\fa=1'b0;\fendmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

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

}  // namespace
