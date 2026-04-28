#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(LexicalConventionSynthesis, FreeFormatCompactSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(f, "module m;logic a;assign a=1'b0;endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(LexicalConventionSynthesis, FreeFormatSpreadSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module\n  m\n;\n  logic\n  a\n;\n  assign\n  a\n=\n1'b0\n;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(LexicalConventionSynthesis, FreeFormatExcessiveWhitespaceSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "  module   m  ;   logic   a  ;   assign  a  =  1'b0  ;   endmodule  ");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(LexicalConventionSynthesis, TabsAndFormfeedsAsWhitespace) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f, "module\tm\f;\flogic\ta\t;\tassign\ta=1'b0;\tendmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(LexicalConventionSynthesis, BlockCommentAsSeparatorSynthesizes) {
  SynthFixture f;
  auto* mod =
      ElaborateSrc(f, "module/**/m;logic/**/a;assign/**/a=1'b0;endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(LexicalConventionSynthesis, CommentsDoNotAffectSynthesis) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module /* block */ m; // line\n"
      "  logic /* type */ a; // decl\n"
      "  assign /* cont */ a = /* rhs */ 1'b0;\n"
      "endmodule /* end */\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

// §5.2: the synthesizable token categories (whitespace, comment, operator,
// number, identifier, keyword) all reach the synth backend in one stream.
// String literals are excluded because synthesis cannot represent them.
TEST(LexicalConventionSynthesis, AllSynthesizableTokenCategoriesSynthesize) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m; // line comment\n"
      "  /* block comment */\n"
      "  logic [7:0] data;\n"
      "  assign data = 8'hAB + 8'd1;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
