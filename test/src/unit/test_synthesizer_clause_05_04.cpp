#include <gtest/gtest.h>

#include "fixture_synthesizer.h"
#include "synthesizer/synth_lower.h"

using namespace delta;

namespace {

TEST(CommentSynthesis, LineCommentSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m; // module\n"
      "  logic a; // var\n"
      "  assign a = 1'b0; // assign\n"
      "endmodule // end\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(CommentSynthesis, BlockCommentSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module /* name */ m /* semi */ ;\n"
      "  logic /* type */ a;\n"
      "  assign /* cont */ a = /* val */ 1'b0;\n"
      "endmodule /* end */\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(CommentSynthesis, MixedCommentsSynthesize) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module /* block */ m; // line\n"
      "  logic a; /* decl */\n"
      "  // assignment\n"
      "  assign a = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(CommentSynthesis, BlockCommentNotNestedSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  logic /* outer /* inner */ a;\n"
      "  assign a = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(CommentSynthesis, LineCommentInsideBlockSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  /* // not special */ logic a;\n"
      "  assign a = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(CommentSynthesis, BlockTokensInsideLineSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f,
      "module m;\n"
      "  // /* not a block comment */\n"
      "  logic a;\n"
      "  assign a = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

TEST(CommentSynthesis, BlockCommentAsSeparatorSynthesizes) {
  SynthFixture f;
  auto* mod = ElaborateSrc(
      f, "module/**/m;logic/**/a;assign/**/a=1'b0;endmodule");
  ASSERT_NE(mod, nullptr);
  SynthLower synth(f.arena, f.diag);
  auto* aig = synth.Lower(mod);
  ASSERT_NE(aig, nullptr);
}

}  // namespace
