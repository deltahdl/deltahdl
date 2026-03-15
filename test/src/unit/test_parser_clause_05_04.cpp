#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(LexicalConventionParsing, CommentDoesNotProduceTokens) {
  auto r = Parse(
      "module m;\n"
      "  // line comment\n"
      "  /* block comment */\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->items.empty());
}

TEST(LexicalConventionParsing, LineCommentAtEofNoNewline) {
  EXPECT_TRUE(ParseOk("module t; endmodule // trailing comment"));
}

TEST(LexicalConventionParsing, AdjacentLineComments) {
  auto r = Parse(
      "module m;\n"
      "  // first comment\n"
      "  // second comment\n"
      "  // third comment\n"
      "  logic a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "a");
}

TEST(LexicalConventionParsing, OneLineCommentEndsAtNewline) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic a; // comment\n"
              "  logic b;\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, BlockCommentBetweenTokens) {
  EXPECT_TRUE(ParseOk("module/* comment */t;/* another */endmodule"));
}

TEST(LexicalConventionParsing, BlockCommentInsideExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, c;\n"
              "  assign a = b /* comment */ + c;\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, BlockCommentSpanningLines) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  /* this comment\n"
              "     spans multiple\n"
              "     lines */\n"
              "  logic a;\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, BlockCommentInLibraryText) {
  auto r = ParseLibrary(
      "/* Multi-line\n"
      "   comment */\n"
      "library lib1 /proj/*.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
}

TEST(LexicalConventionParsing, LineCommentTokenInsideBlockComment) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  /* // not special */ logic a;\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, BlockCommentStartInsideLineComment) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  // this /* is not special\n"
              "  logic a;\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, NestedBlockCommentClosesAtFirstEnd) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic /* outer /* inner */ a;\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, EmptyCuCommentsOnly) {
  auto r = Parse(
      "// line comment\n"
      "/* block\n"
      "   comment */\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.cu->modules.empty());
  EXPECT_TRUE(r.cu->packages.empty());
}

TEST(LexicalConventionParsing, CommentsDoNotAffectParseResult) {
  auto with = Parse(
      "module /* block */ t; // line\n"
      "  logic a;\n"
      "endmodule\n");
  auto without = Parse(
      "module t;\n"
      "  logic a;\n"
      "endmodule\n");
  ASSERT_NE(with.cu, nullptr);
  ASSERT_NE(without.cu, nullptr);
  EXPECT_FALSE(with.has_errors);
  EXPECT_FALSE(without.has_errors);
  ASSERT_EQ(with.cu->modules.size(), 1u);
  ASSERT_EQ(without.cu->modules.size(), 1u);
  EXPECT_EQ(with.cu->modules[0]->name, without.cu->modules[0]->name);
}

TEST(LexicalConventionParsing, UnterminatedBlockCommentCausesParseError) {
  EXPECT_FALSE(ParseOk("module t; /* unterminated comment endmodule"));
}

TEST(LexicalConventionParsing, CommentsInPackageDeclaration) {
  EXPECT_TRUE(
      ParseOk("package /* block */ p; // line\n"
              "  typedef logic [7:0] byte_t; // type\n"
              "endpackage /* end */\n"));
}

}  // namespace
