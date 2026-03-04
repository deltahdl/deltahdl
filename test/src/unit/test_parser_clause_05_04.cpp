// §5.4: Comments

#include "fixture_config.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

// =========================================================================
// Section 5.6.3: System tasks and system functions
// =========================================================================
namespace {

// =========================================================================
// Comments do NOT produce tokens
// =========================================================================
TEST(ParserCh501, Sec5_1_CommentDoesNotProduceTokens) {
  // A module containing only comments and no actual items parses cleanly.
  auto r = Parse(
      "module m;\n"
      "  // line comment\n"
      "  /* block comment */\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->items.empty());
}

// =========================================================================
// Line comment at end of file (no trailing newline)
// =========================================================================
TEST(ParserCh501, Sec5_1_LineCommentAtEofNoNewline) {
  // A line comment at EOF without a trailing newline must still parse.
  EXPECT_TRUE(ParseOk("module t; endmodule // trailing comment"));
}

// =========================================================================
// Block comment between tokens
// =========================================================================
TEST(ParserCh501, Sec5_1_BlockCommentBetweenTokens) {
  // Block comment placed between keyword tokens acts as whitespace.
  EXPECT_TRUE(ParseOk("module/* comment */t;/* another */endmodule"));
}

// =========================================================================
// Block comment inside expression (splitting operator from operand)
// =========================================================================
TEST(ParserCh501, Sec5_1_BlockCommentInsideExpression) {
  // Block comment between operands in a continuous assignment expression.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, c;\n"
              "  assign a = b /* comment */ + c;\n"
              "endmodule\n"));
}

// =========================================================================
// Nested /* inside line comment (not special)
// =========================================================================
TEST(ParserCh501, Sec5_1_NestedBlockCommentStartInsideLineComment) {
  // A /* inside a // comment is not treated as the start of a block comment.
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  // this /* is not special\n"
              "  logic a;\n"
              "endmodule\n"));
}

// =========================================================================
// Section 5.6: Identifiers, keywords, and system names
// =========================================================================
// =========================================================================
// Adjacent line comments
// =========================================================================
TEST(ParserCh501, Sec5_1_AdjacentLineComments) {
  // Multiple consecutive line comments behave as whitespace.
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
using DpiParseTest = ProgramTestParse;

// Block comments.
TEST(LibraryText, BlockComments) {
  auto r = ParseLibrary(
      "/* Multi-line\n"
      "   comment */\n"
      "library lib1 /proj/*.v;\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
}

TEST(ParserCh501, Sec5_1_EmptyCuCommentsOnly) {
  // A compilation unit containing only comments parses to an empty CU.
  auto r = Parse(
      "// line comment\n"
      "/* block\n"
      "   comment */\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.cu->modules.empty());
  EXPECT_TRUE(r.cu->packages.empty());
}

TEST(ParserCh503, BlockCommentSpanningLines) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  /* this comment\n"
              "     spans multiple\n"
              "     lines */\n"
              "  logic a;\n"
              "endmodule\n"));
}

TEST(ParserCh503, OneLineCommentEndsAtNewline) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic a; // comment\n"
              "  logic b;\n"
              "endmodule\n"));
}

}  // namespace
