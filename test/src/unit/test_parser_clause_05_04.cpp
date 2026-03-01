// §5.4: Comments

#include "fixture_parser.h"

using namespace delta;

// =========================================================================
// Section 5.6.3: System tasks and system functions
// =========================================================================
struct ParseResult50603 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult50603 Parse(const std::string& src) {
  ParseResult50603 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

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
struct ParseResult506 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ModuleItem* FirstItem(ParseResult506& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

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

struct ConfigTest : ::testing::Test {
 protected:
  CompilationUnit* Parse(const std::string& src) {
    source_ = src;
    lexer_ = std::make_unique<Lexer>(source_, 0, diag_);
    parser_ = std::make_unique<Parser>(*lexer_, arena_, diag_);
    return parser_->Parse();
  }

  bool HasErrors() const { return diag_.HasErrors(); }

  SourceManager mgr_;
  Arena arena_;
  DiagEngine diag_{mgr_};
  std::string source_;
  std::unique_ptr<Lexer> lexer_;
  std::unique_ptr<Parser> parser_;
};

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

}  // namespace
