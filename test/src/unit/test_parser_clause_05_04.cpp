#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserClause05, Cl5_4_CommentDoesNotProduceTokens) {
  auto r = Parse(
      "module m;\n"
      "  // line comment\n"
      "  /* block comment */\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->items.empty());
}

TEST(ParserClause05, Cl5_4_LineCommentAtEofNoNewline) {
  EXPECT_TRUE(ParseOk("module t; endmodule // trailing comment"));
}

TEST(ParserClause05, Cl5_4_AdjacentLineComments) {
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

TEST(ParserClause05, Cl5_4_OneLineCommentEndsAtNewline) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic a; // comment\n"
              "  logic b;\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_4_BlockCommentBetweenTokens) {
  EXPECT_TRUE(ParseOk("module/* comment */t;/* another */endmodule"));
}

TEST(ParserClause05, Cl5_4_BlockCommentInsideExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, c;\n"
              "  assign a = b /* comment */ + c;\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_4_BlockCommentSpanningLines) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  /* this comment\n"
              "     spans multiple\n"
              "     lines */\n"
              "  logic a;\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_4_BlockCommentInLibraryText) {
  auto r = ParseLibrary(
      "/* Multi-line\n"
      "   comment */\n"
      "library lib1 /proj/*.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
}

TEST(ParserClause05, Cl5_4_LineCommentTokenInsideBlockComment) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  /* // not special */ logic a;\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_4_BlockCommentStartInsideLineComment) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  // this /* is not special\n"
              "  logic a;\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_4_NestedBlockCommentClosesAtFirstEnd) {

  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic /* outer /* inner */ a;\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_4_EmptyCuCommentsOnly) {
  auto r = Parse(
      "// line comment\n"
      "/* block\n"
      "   comment */\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.cu->modules.empty());
  EXPECT_TRUE(r.cu->packages.empty());
}

}
