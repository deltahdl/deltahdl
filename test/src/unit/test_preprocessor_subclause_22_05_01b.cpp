#include <gtest/gtest.h>

#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"

using namespace delta;

// §22.5.1 requires the actual arguments of a usage to be enclosed in
// parentheses and separated by commas, and places them on no particular line,
// so a list left open at the end of a physical line continues on the next one.
// The usage stands after other text so that it is read by the inline
// expander; the one below stands at the head of its line and is read by the
// directive path, which reaches the arguments through its own code.
TEST(Preprocessor, FunctionLikeUsageArgumentsContinueOnTheNextLine) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define PAIR(a, b) a b\n"
      "int x = `PAIR(1,\n"
      "  2);\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 1 2;"), std::string::npos);
  EXPECT_EQ(result.find('`'), std::string::npos);
}

// The shape of uvm_misc.svh:635 in the UVM library sv-tests ships: the usage
// heads its line, and the line ends inside a {...} concatenation that is the
// second argument, so the comma ending the line is one the matched braces
// protect rather than a separator, and the argument runs to the brace that
// closes on the next line.
TEST(Preprocessor, UsageSplitInsideAConcatenationArgument) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define WARN(ID, MSG) report(ID, MSG);\n"
      "`WARN(\"find_type-no match\",{\"Instance of type '\",name,\n"
      "\" not found in component hierarchy beginning at \",start})\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("report(\"find_type-no match\", {\"Instance of type "
                        "'\",name, \" not found in component hierarchy "
                        "beginning at \",start});"),
            std::string::npos);
}

// The parentheses that decide whether the list is open are the ones in code:
// a one-line comment ending the first line holds one that never closes, and
// counting it would carry the join past the line that closes the list.
TEST(Preprocessor, CommentOnTheFirstLineOfASplitUsageIsNotCounted) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define PAIR(a, b) a b\n"
      "int x = `PAIR(1, // (\n"
      "  2);\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 1 2"), std::string::npos);
}

// §22.13 has `__LINE__ expand to the current input line number, and a usage
// that spans two lines is one construct standing on the line it opened on, so
// a `__LINE__ among its arguments names that line rather than the one the
// argument was written on.
TEST(Preprocessor, LineInsideASplitUsageIsTheLineTheUsageOpenedOn) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define AT(a, b) a b\n"
      "int x = `AT(1,\n"
      "  `__LINE__);\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 1 2;"), std::string::npos);
}

// The lines a usage ran onto are still lines of the file, so a report about
// the line after it names the line the user wrote, not the line the usage
// opened on plus one.
TEST(Preprocessor, LineAfterASplitUsageKeepsItsOwnNumber) {
  PreprocFixture f;
  Preprocess(
      "`define PAIR(a, b) a b\n"
      "int x = `PAIR(1,\n"
      "  2);\n"
      "`NOPE\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undefined macro 'NOPE'", 4,
                            "22.5.1"));
}

// A list that no later line closes is left as written: the line is processed
// alone and the lines after it stay their own, rather than the rest of the
// file being read as the usage's arguments.
TEST(Preprocessor, UsageNeverClosedLeavesTheLinesAfterItAlone) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define PAIR(a, b) a b\n"
      "int x = `PAIR(1,\n"
      "int y;\n",
      f);
  EXPECT_NE(result.find("int x = `PAIR(1,\nint y;\n"), std::string::npos);
}

// A list left open on the last line of the file has no line to continue on,
// and is left as written like any other list no later line closes.
TEST(Preprocessor, UsageOpenOnTheLastLineIsLeftAsWritten) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define PAIR(a, b) a b\n"
      "int x = `PAIR(1,",
      f);
  EXPECT_NE(result.find("int x = `PAIR(1,"), std::string::npos);
}

// The list a usage continues is one that opens at the name: text of another
// kind after the name is not an argument list left open, so nothing is read
// ahead for it, and the usage is rejected as one written without parentheses.
TEST(Preprocessor, FunctionLikeMacroFollowedByOtherTextRequiresParentheses) {
  PreprocFixture f;
  Preprocess(
      "`define FUNC(a=5) a\n"
      "`FUNC;\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parentheses required for function-like macro "
                            "'FUNC'",
                            2, "22.5.1"));
}

// A `define body is arbitrary text: a list it leaves open is closed by
// whatever usage the body is written to pair with, so the line after the
// definition is not joined into it.
TEST(Preprocessor, DefineBodyLeavingAListOpenTakesNoFollowingLine) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define OPEN(a) `PAIR(a,\n"
      "int y;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\nint y;\n"), std::string::npos);
}

// A directive at the head of a line after an open list is not read as part of
// the arguments: the conditional it opens has to act on the lines after it,
// which it could not from inside an argument. The usage is left as written,
// and the line the conditional excludes stays excluded.
TEST(Preprocessor, DirectiveLineAfterAnOpenUsageIsNotReadAsAnArgument) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define PAIR(a, b) a b\n"
      "int x = `PAIR(1,\n"
      "`ifdef NOPE\n"
      "  2);\n"
      "`endif\n",
      f);
  EXPECT_NE(result.find("int x = `PAIR(1,\n"), std::string::npos);
  EXPECT_EQ(result.find("2);"), std::string::npos);
}

// A line inside a triple_quoted_string opened on an earlier line (A.8.8) is
// the string's content, so what looks like an open usage on it starts no join
// and the lines after it stay their own.
TEST(Preprocessor, UsageInsideATripleQuotedStringIsNotJoined) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define PAIR(a, b) a b\n"
      "string s = \"\"\"\n"
      "`PAIR(1,\n"
      "2)\"\"\";\n"
      "int y;\n",
      f);
  EXPECT_NE(result.find("`PAIR(1,\n2)\"\"\";\nint y;\n"), std::string::npos);
}

// §22.13's `__LINE__ stands for a value where it is written, so one among the
// actual arguments of a usage on a single line is an argument and not a
// directive the line is split at: the usage expands whole, with the line
// number substituted for it.
TEST(Preprocessor, LineAmongTheArgumentsOfAOneLineUsageIsAnArgument) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define AT(a, b) a b\n"
      "int x = `AT(1, `__LINE__);\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 1 2;"), std::string::npos);
}

// §22.5.1 allows white space between the text macro name and the left
// parenthesis of a usage, and §5.3 makes a newline white space, so a name
// ending one line and its argument list opening the next are one usage.
TEST(Preprocessor, ArgumentListOpeningOnTheLineAfterTheName) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define PAIR(a, b) a b\n"
      "int x = `PAIR\n"
      "  (1, 2);\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 1 2;"), std::string::npos);
}

// Between the name and the parenthesis §5.3's white space and §5.4's one-line
// comment are separators, not tokens, so a blank line and a comment line
// between the two are read through to the list.
TEST(Preprocessor, BlankAndCommentLinesBetweenTheNameAndItsList) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define PAIR(a, b) a b\n"
      "int x = `PAIR // list below\n"
      "\n"
      "  // the list\n"
      "  (1, 2);\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 1 2;"), std::string::npos);
}

// A name ending a line whose next line opens no list is a usage written without
// its parentheses, which §22.5.1 requires: nothing is read ahead for it, the
// usage is rejected where it stands, and the line after it stays its own.
TEST(Preprocessor, NameAloneBeforeALineOpeningNoListIsRejected) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FUNC(a=5) a\n"
      "`FUNC\n"
      "int y;\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parentheses required for function-like macro "
                            "'FUNC'",
                            2, "22.5.1"));
  EXPECT_NE(result.find("\nint y;\n"), std::string::npos);
}

// §22.5.1 lists triple quotes among the matched pairs a comma is protected
// inside, and A.8.8 makes a lone '"' an item of a triple_quoted_string rather
// than its end, so the '"' and the ',' inside the first argument here are text
// and the usage has two arguments, not three.
TEST(Preprocessor, TripleQuotedArgumentKeepsItsQuoteAndComma) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M(a, b) $display(a, b);\n"
      "`M(\"\"\"say \"hi\", now\"\"\", 1)\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("$display(\"\"\"say \"hi\", now\"\"\", 1);"),
            std::string::npos);
}

// The same pair protects a right parenthesis: the ')' inside the triple-quoted
// argument does not end the list, which ends at the ')' after the second
// argument.
TEST(Preprocessor, TripleQuotedArgumentKeepsItsRightParenthesis) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M(a, b) $display(a, b);\n"
      "`M(\"\"\"a) b\"\"\", 2)\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("$display(\"\"\"a) b\"\"\", 2);"), std::string::npos);
}

// An escaped identifier (5.6.1) is also among the pairs, and runs to the next
// white space, so the ')' inside \a)b is part of the identifier and the list
// ends at the ')' after it.
TEST(Preprocessor, EscapedIdentifierArgumentKeepsItsRightParenthesis) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define ID(x) x\n"
      "assign `ID(\\a)b ) = 1;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("assign \\a)b = 1;"), std::string::npos);
}

// A default text is protected by the same pairs as an actual argument, so a
// triple-quoted default holding a comma and a right parenthesis is one default
// and the formal list still closes at its own parenthesis.
TEST(Preprocessor, TripleQuotedDefaultTextIsOneDefault) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define D(a = \"\"\"x,)y\"\"\") [a]\n"
      "`D()\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("[\"\"\"x,)y\"\"\"]"), std::string::npos);
}

// A '"' preceded by a backslash inside a quoted_string is 5.9's escape
// sequence and closes nothing, so the comma after it is still inside the
// string and the usage has two arguments.
TEST(Preprocessor, EscapedQuoteInsideAStringArgumentClosesNothing) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M(a, b) $display(a, b);\n"
      "`M(\"q\\\"x,y\", 1)\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("$display(\"q\\\"x,y\", 1);"), std::string::npos);
}

// The same rejection after other text on the line: the inline expander used to
// leave a function-like name without its list for the lexer to report as a
// stray backtick, which named the character rather than the rule.
TEST(Preprocessor, FunctionLikeMacroWithoutParenthesesAfterTextIsRejected) {
  PreprocFixture f;
  Preprocess(
      "`define FUNC(a=5) a\n"
      "int x = `FUNC + 1;\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parentheses required for function-like macro "
                            "'FUNC'",
                            2, "22.5.1"));
}

// §22.5.1 (printed page 710) lets the macro text contain usages of other text
// macros, substituted after the outer macro is substituted, and separately has
// a compiler directive written in that text take effect when the macro is
// used. A backtick opens either one, and item a) of the same page is what
// parts them: a text macro name shall not be the same as a compiler directive
// keyword. The shape below is uvm_tlm_imps.svh:177 of the UVM library sv-tests
// ships, where `UVM_GET_PEEK_IMP is two usages on two lines and nothing else;
// read as a compiler directive because of the backtick alone, neither of them
// reached the output and the class the file declares lost its methods.
TEST(Preprocessor, MacroTextOpeningWithAnotherUsageExpandsEveryLineOfIt) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define GET(arg) task get(output int arg); endtask\n"
      "`define PEEK(arg) task peek(output int arg); endtask\n"
      "`define GET_PEEK(arg) \\\n"
      "  `GET(arg) \\\n"
      "  `PEEK(arg)\n"
      "`GET_PEEK(t)\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("task get(output int t); endtask"), std::string::npos);
  EXPECT_NE(result.find("task peek(output int t); endtask"), std::string::npos);
  EXPECT_EQ(result.find('`'), std::string::npos);
}
