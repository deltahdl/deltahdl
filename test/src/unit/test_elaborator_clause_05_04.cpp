#include "fixture_elaborator.h"

namespace {

TEST(LexicalConventionElaboration, CommentsDoNotAffectElaboration) {
  EXPECT_TRUE(
      ElabOk("module /* block */ t; // line comment\n"
             "  logic /* type */ a; // declaration\n"
             "  assign /* continuous */ a = /* rhs */ 1'b1;\n"
             "endmodule /* end */\n"));
}

TEST(LexicalConventionElaboration, LineCommentsOnlyElaborates) {
  EXPECT_TRUE(
      ElabOk("module t; // module\n"
             "  logic a; // var\n"
             "  assign a = 1'b0; // assign\n"
             "endmodule // end\n"));
}

TEST(LexicalConventionElaboration, BlockCommentSpanningLinesElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  /* this comment\n"
             "     spans multiple\n"
             "     lines */\n"
             "  logic a;\n"
             "  assign a = 1'b0;\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, BlockCommentNotNestedElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic /* outer /* inner */ a;\n"
             "  assign a = 1'b1;\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, LineCommentInsideBlockIgnoredElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  /* // not a line comment\n"
             "     still block */\n"
             "  logic a;\n"
             "  assign a = 1'b0;\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, BlockTokensInsideLineIgnoredElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  // /* not a block comment */\n"
             "  logic a;\n"
             "  assign a = 1'b1;\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, MixedCommentsElaborate) {
  EXPECT_TRUE(
      ElabOk("module /* name */ t; // header\n"
             "  logic a; /* decl */\n"
             "  // assignment below\n"
             "  assign /* lhs */ a = /* rhs */ 1'b0; // done\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, CommentOnlyInputElaboratesEmpty) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "// only comments\n"
      "/* block\n"
      "   comment */\n",
      f);
  EXPECT_EQ(design, nullptr);
}

TEST(LexicalConventionElaboration, CommentsInAlwaysBlockElaborate) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic a, b;\n"
             "  always_comb begin // combinational\n"
             "    a = /* invert */ ~b; // assign\n"
             "  end /* end always */\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, CommentsAroundContinuousAssignElaborate) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic a;\n"
             "  /* before */ assign /* mid */ a /* eq */ = /* val */ 1'b0 "
             "/* semi */ ; /* after */\n"
             "endmodule\n"));
}

}  // namespace
