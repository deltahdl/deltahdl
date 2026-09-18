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
