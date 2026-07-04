#include "fixture_parser.h"

// §A.9.4 white_space ::= space | tab | newline | formfeed | eof
//
// White space is a lexer-stage rule: it separates adjacent tokens and is
// otherwise discarded. These tests observe that separation flowing downstream
// into the parser — the same module parses into a valid AST no matter which
// white_space alternative delimits its tokens, and the final `eof` closes the
// token stream without a spurious trailing construct.

namespace {

TEST(WhiteSpaceParsing, SpaceDelimiterParses) {
  EXPECT_TRUE(ParseOk("module t; logic a; assign a = 1'b0; endmodule"));
}

TEST(WhiteSpaceParsing, TabDelimiterParses) {
  EXPECT_TRUE(ParseOk("module\tt;\tlogic\ta;\tassign\ta=1'b0;\tendmodule"));
}

TEST(WhiteSpaceParsing, NewlineDelimiterParses) {
  EXPECT_TRUE(
      ParseOk("module\nt\n;\nlogic\na\n;\nassign\na\n=\n1'b0\n;\nendmodule\n"));
}

TEST(WhiteSpaceParsing, FormfeedDelimiterParses) {
  EXPECT_TRUE(ParseOk("module\ft\f;\flogic\fa\f;\fassign\fa=1'b0;\fendmodule"));
}

TEST(WhiteSpaceParsing, EmptyInputParsesEmptyCompilationUnit) {
  // A source of only implicit eof yields a valid, empty compilation unit.
  auto result = Parse("");
  EXPECT_FALSE(result.has_errors);
  ASSERT_NE(result.cu, nullptr);
}

}  // namespace
