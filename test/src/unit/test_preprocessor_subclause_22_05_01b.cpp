#include <gtest/gtest.h>

#include <cstddef>
#include <filesystem>
#include <fstream>
#include <string>

#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"

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

// §22.5.1 lets a default contain a comma inside a matched pair of parentheses,
// where it separates the default's own arguments rather than two formal
// arguments. The macro therefore has two formal arguments, and the first,
// left empty, takes the whole of its default.
TEST(Preprocessor, CommaInsideAParenthesizedDefaultSeparatesNoArguments) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M(a = f(1, 2), b = 0) a + b\n"
      "x = `M(, 3);\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("x = f(1, 2) + 3;"), std::string::npos) << result;
}

// §22.5.1: argument substitution does not occur within a string literal, and
// §5.9's escaped quotation mark inside one closes nothing, so a formal
// argument's name after it is still inside the string and left as written.
TEST(Preprocessor, AnEscapedQuoteInsideAMacroTextStringClosesNothing) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M(x) \"say \\\"x\\\" to x\" x\n"
      "`M(1)\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\"say \\\"x\\\" to x\" 1"), std::string::npos)
      << result;
}

// A directory holding one include file, `name` with `text`, removed when the
// case is over.
class OneIncludeFile {
 public:
  OneIncludeFile(const char* dir, const char* name, const char* text)
      : dir_(std::filesystem::temp_directory_path() / dir) {
    std::filesystem::create_directories(dir_);
    std::ofstream(dir_ / name) << text;
  }
  ~OneIncludeFile() { std::filesystem::remove_all(dir_); }
  OneIncludeFile(const OneIncludeFile&) = delete;
  OneIncludeFile& operator=(const OneIncludeFile&) = delete;
  PreprocConfig Config() const {
    PreprocConfig cfg;
    cfg.include_dirs.push_back(dir_.string());
    return cfg;
  }

 private:
  std::filesystem::path dir_;
};

// §22.5.1 makes a macro recursive where it expands directly or indirectly to
// text holding a usage of itself. INC's text is an `include, and the file it
// brings in uses INC at the head of a line, so INC reaches its own usage
// through the file; that usage is read by the directive path while INC is
// still being expanded.
TEST(Preprocessor, AUsageInAFileTheMacroIncludesIsRecursive) {
  OneIncludeFile inc("dhl_22_05_01b_self_inc", "self.svh", "`INC\n");
  PreprocFixture f;
  Preprocess(
      "`define INC `include \"self.svh\"\n"
      "`INC\n",
      f, inc.Config());
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "recursive expansion of macro 'INC'", 1, "22.5.1"));
}

// §22.5.1 has a directive in a macro's text take effect where the macro is
// used, and the text INC substitutes is an `include with no file name. The
// rest of the usage's line supplies it, so the two together are the one
// directive §22.4 reads.
TEST(Preprocessor, TheRestOfTheLineCompletesADirectiveTheMacroOpened) {
  OneIncludeFile inc("dhl_22_05_01b_rest", "body.svh", "included_text\n");
  PreprocFixture f;
  auto result = Preprocess(
      "`define INC `include\n"
      "`INC \"body.svh\"\n",
      f, inc.Config());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("included_text"), std::string::npos);
}

// The rest of the line opens with a backtick of its own, so it is read after
// the `include as a line of its own. It names no directive and no macro, so
// it is the usage of an undefined macro §22.5.1 makes an error, and the
// `include before it still takes effect.
TEST(Preprocessor, AnUndefinedUsageAfterAnIncludeTheMacroOpenedIsReported) {
  OneIncludeFile inc("dhl_22_05_01b_undef", "body.svh", "included_text\n");
  PreprocFixture f;
  auto result = Preprocess(
      "`define INC `include \"body.svh\"\n"
      "`INC `NOPE\n",
      f, inc.Config());
  EXPECT_NE(result.find("included_text"), std::string::npos);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undefined macro 'NOPE'", 2,
                            "22.5.1"));
}

// A grave accent opens the `" and `\`" of §22.5.1 only with those characters
// after it, so macro text ending in one, or holding `\ followed by anything
// else, opens no string literal and is not reported as an unterminated one.
TEST(Preprocessor, GraveAccentOpeningNoMacroQuoteOpensNoString) {
  for (const char* text : {"a`", "`\\xyz", "`\\`xy"}) {
    PreprocFixture f;
    Preprocess(std::string("`define M ") + text + "\n", f);
    EXPECT_FALSE(f.diag.HasErrors()) << text;
  }
}

// Inside a triple-quoted string a pair of quotes that a third does not follow
// closes nothing, and an escaped quote inside an ordinary string closes
// nothing either; both macros are complete and substitute their text whole.
TEST(Preprocessor, QuotesThatCloseNoStringInMacroText) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define TRIPLE \"\"\"ab\"\"c\"\"\"\n"
      "`define ESCAPED \"a\\\"b\"\n"
      "x `TRIPLE `ESCAPED y\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("x \"\"\"ab\"\"c\"\"\" \"a\\\"b\" y"),
            std::string::npos);
}

// §22.5.1 keeps a comment out of the substituted text, and a quote inside a
// block comment is comment text, so it opens no string that would carry the
// macro text past the comment's close.
TEST(Preprocessor, QuoteInsideABlockCommentInMacroTextOpensNoString) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M a /* \" */ b\n"
      "x `M y\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("x a"), std::string::npos);
  EXPECT_NE(result.find("b y"), std::string::npos);
}

// A backslash asks for the macro text to go on over the next line, and the
// end of the source ends it all the same: on the source's last line, or on a
// last line the backslash carried the text onto. The macros stay defined for
// the next source the same run reads.
TEST(Preprocessor, BackslashContinuationRunningToTheEndOfTheSource) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  pp.Preprocess(f.mgr.AddFile("first.sv", "`define ENDS a \\"));
  pp.Preprocess(f.mgr.AddFile("second.sv", "`define CARRIED c \\\nd"));
  auto result =
      pp.Preprocess(f.mgr.AddFile("third.sv", "x `ENDS `CARRIED y\n"));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("x a"), std::string::npos);
  EXPECT_NE(result.find('c'), std::string::npos);
  EXPECT_NE(result.find("d y"), std::string::npos);
}

// An argument list still open at the end of a line goes on over a line that
// holds only another macro's usage, which is an argument rather than a
// directive the join has to leave standing.
TEST(Preprocessor, ArgumentsContinueOverALineHoldingOnlyAUsage) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define PAIR(a, b) a b\n"
      "`define ONE 1\n"
      "int x = `PAIR(1,\n"
      "`ONE\n"
      ");\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 1 1;"), std::string::npos);
}

// §22.5.1 (printed page 710) forbids macro substitution within a string
// literal. After each usage it expands, the inline expander recounts the quotes
// from the start of the line to learn whether what follows is inside a string,
// so a line whose very first character opens a string still has the usage
// after that string expanded and the usage inside the next string kept.
TEST(Preprocessor, LineOpeningWithAStringKeepsLaterStringsUnexpanded) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define ONE 1\n"
      "\"a\" `ONE \"`ONE\" `ONE\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\"a\" 1 \"`ONE\" 1"), std::string::npos);
}

// The same recount steps over a quote a backslash escapes, which stands inside
// the string rather than closing it, so the string holding it still ends at
// its own closing quote.
TEST(Preprocessor, EscapedQuoteBeforeAUsageClosesNoString) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define ONE 1\n"
      "x = \"a\\\"b\" `ONE \"`ONE\" `ONE\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("x = \"a\\\"b\" 1 \"`ONE\" 1"), std::string::npos);
}

// A block comment in the macro text is not part of the text substituted, and it
// runs to the first "*/": an asterisk inside it that no slash follows does not
// end it.
TEST(Preprocessor, AsteriskInsideAMacroTextBlockCommentEndsNothing) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M a /* x*y */ b\n"
      "int v = `M;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("x*y"), std::string::npos);
  EXPECT_EQ(result.find("y */"), std::string::npos);
  EXPECT_NE(result.find("int v = a"), std::string::npos);
  EXPECT_NE(result.find("b;"), std::string::npos);
}

// A function-like macro's name ending the source after other text has no line
// after it to carry its list, so the usage is rejected as one written without
// the parentheses §22.5.1 requires.
TEST(Preprocessor, FunctionLikeNameEndingTheSourceAfterTextIsRejected) {
  PreprocFixture f;
  Preprocess(
      "`define FUNC(a=5) a\n"
      "int x = `FUNC",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "parentheses required for function-like macro "
                            "'FUNC'",
                            2, "22.5.1"));
}

// §22.5.1 (Syntax 22-2): a text macro definition names its macro, with an
// identifier, simple or escaped, so a `define with nothing after it or with a
// name no identifier can open is reported. Each was accepted without a word.
TEST(Preprocessor, DefineMissingItsNameIsReported) {
  for (const char* directive : {"`define\n", "`define 5 x\n"}) {
    PreprocFixture f;
    Preprocess(directive, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "`define is missing its macro name", 1, "22.5.1"))
        << directive;
  }
}

// §22.5.1 (Syntax 22-2): a `(` after the macro name opens a formal argument
// list a `)` closes, so one never closed is reported and defines nothing. M was
// defined as an empty object-like macro, its usage expanding to nothing.
TEST(Preprocessor, UnclosedFormalArgumentListIsReported) {
  PreprocFixture f;
  Preprocess("`define M(a, b\nx y\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "formal argument list of `define M is never closed",
                            1, "22.5.1"));
}

// §5.4: a block comment is closed by */, so the macro text of a `define on the
// last line opening one is reported as the same text outside a `define is.
// The comment was dropped and M defined as a.
TEST(Preprocessor, UnterminatedBlockCommentInMacroTextIsReported) {
  PreprocFixture f;
  Preprocess("`define M a /* x", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "unterminated block comment",
                            1, "5.4"));
}

// §22.5.1: an unclosed triple-quoted string leaves the `define open to the end
// of the source, and the report belongs at the `define, line 2, as an unclosed
// ordinary string's is. It was given at line 6, past the end of the file.
TEST(Preprocessor, UnclosedTripleQuoteReportedAtTheDefine) {
  PreprocFixture f;
  Preprocess(
      "module m;\n"
      "`define M \"\"\"abc\"\n"
      "wire a;\n"
      "wire b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unterminated string literal in macro body", 2,
                            "22.5.1"));
}

// §22.5.1 with §5.9: a newline inside a triple-quoted string is part of the
// string and does not end the macro text, so the expansion carries the string
// with its newlines. Each was dropped, joining the lines into one.
TEST(Preprocessor, TripleQuotedStringInMacroTextKeepsItsNewlines) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define TEST \"\"\"\n"
      "many\n"
      "more\n"
      "lines\"\"\"\n"
      "x = `TEST;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("\"\"\"\nmany\nmore\nlines\"\"\""), std::string::npos)
      << out;
}

// §22.5.1: between `" and `" a macro usage is expanded, as a formal is
// substituted, so `N in `"N=`N`" gives N=7. It reached the lexer unexpanded,
// the `" taken for a string's opening quote.
TEST(Preprocessor, UsageBetweenMacroQuotesIsExpanded) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define N 7\n"
      "`define T `\"N=`N`\"\n"
      "x = `T;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(out.find("N=7"), std::string::npos) << out;
  EXPECT_EQ(out.find("`N"), std::string::npos) << out;
}

// §22.6 with §22.5.1: a conditional in macro text is read at each usage, and
// an `elsif whose condition holds selects its group, a name or a
// parenthesized expression; with none holding and no `else, nothing. The
// `else group was taken whenever the `ifdef failed.
TEST(Preprocessor, ElsifInMacroTextSelectsItsGroup) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define PICK(x) `ifdef DOUBLE (x)*2 `elsif TRIPLE (x)*3 `else (x) "
      "`endif\n"
      "`define PICK2 `ifdef DOUBLE 2 `elsif (TRIPLE) 3 `endif\n"
      "`define PICK3 `ifdef DOUBLE 2 `elsif QUAD 4 `endif\n"
      "`define TRIPLE\n"
      "a = `PICK(10);\n"
      "b = `PICK2;\n"
      "c = `PICK3;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  // The text a usage left on its line, `name = ` up to the semicolon.
  auto line_of = [&out](const std::string& name) {
    size_t at = out.find(name + " =");
    return at == std::string::npos ? std::string("<missing>")
                                   : out.substr(at, out.find(';', at) - at);
  };
  EXPECT_NE(line_of("a").find("(10)*3"), std::string::npos) << out;
  EXPECT_NE(line_of("b").find('3'), std::string::npos) << out;
  EXPECT_EQ(line_of("c").find_first_of("24"), std::string::npos) << out;
}
