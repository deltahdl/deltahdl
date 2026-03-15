#include "fixture_elaborator.h"

namespace {

TEST(LexicalConventionElaboration, FreeFormatCompactElaborates) {
  EXPECT_TRUE(ElabOk("module t;logic a;assign a=1'b0;endmodule"));
}

TEST(LexicalConventionElaboration, FreeFormatSpreadElaborates) {
  EXPECT_TRUE(
      ElabOk("module\n  t\n;\n  logic\n  a\n;\n  assign\n  a\n=\n1'b0\n;\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, FreeFormatWhitespaceVariationsElaborateIdentically) {
  ElabFixture f1;
  auto* compact = ElaborateSrc("module t;logic a;assign a=1'b0;endmodule", f1);
  ElabFixture f2;
  auto* spread = ElaborateSrc(
      "module\n  t\n;\n  logic\n  a\n;\n  assign\n  a\n=\n1'b0\n;\n"
      "endmodule\n",
      f2);
  ASSERT_NE(compact, nullptr);
  ASSERT_NE(spread, nullptr);
  EXPECT_FALSE(f1.has_errors);
  EXPECT_FALSE(f2.has_errors);
}

TEST(LexicalConventionElaboration, FreeFormatExcessiveWhitespaceElaborates) {
  EXPECT_TRUE(
      ElabOk("  module   t  ;   logic   a  ;   assign  a  =  1'b0  ;   "
             "endmodule  "));
}

TEST(LexicalConventionElaboration, TabsAndFormfeedsAsWhitespace) {
  EXPECT_TRUE(ElabOk("module\tt\f;\flogic\ta\t;\tendmodule"));
}

TEST(LexicalConventionElaboration, EscapedIdentifierElaboratesCorrectly) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic \\my+sig ;\n"
      "  assign \\my+sig = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LexicalConventionElaboration, EscapedKeywordAsIdentifierElaborates) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  logic \\module ;\n"
             "  assign \\module = 1'b0;\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, AllTokenCategoriesElaborate) {
  EXPECT_TRUE(
      ElabOk("module t; // line comment\n"
             "  /* block comment */\n"
             "  logic [7:0] data = 8'hAB;\n"
             "  initial $display(\"hello\");\n"
             "endmodule\n"));
}

TEST(LexicalConventionElaboration, BlockCommentAsSeparatorElaborates) {
  EXPECT_TRUE(
      ElabOk("module/**/t;logic/**/a;assign/**/a=1'b0;endmodule"));
}

TEST(LexicalConventionElaboration, CommentsDoNotAffectElaborationResult) {
  ElabFixture f1;
  auto* without = ElaborateSrc("module t; logic a; endmodule", f1);
  ElabFixture f2;
  auto* with = ElaborateSrc(
      "module /* block */ t; // line\n"
      "  logic /* type */ a; // decl\n"
      "endmodule /* end */\n",
      f2);
  ASSERT_NE(without, nullptr);
  ASSERT_NE(with, nullptr);
  EXPECT_FALSE(f1.has_errors);
  EXPECT_FALSE(f2.has_errors);
}

}  // namespace
