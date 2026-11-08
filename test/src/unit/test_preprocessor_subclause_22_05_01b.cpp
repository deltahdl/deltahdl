#include <gtest/gtest.h>

#include <cstddef>
#include <filesystem>
#include <fstream>
#include <string>

#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

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

TEST(Preprocessor, UsageNeverClosedLeavesTheLinesAfterItAlone) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define PAIR(a, b) a b\n"
      "int x = `PAIR(1,\n"
      "int y;\n",
      f);
  EXPECT_NE(result.find("int x = `PAIR(1,\nint y;\n"), std::string::npos);
}

TEST(Preprocessor, UsageOpenOnTheLastLineIsLeftAsWritten) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define PAIR(a, b) a b\n"
      "int x = `PAIR(1,",
      f);
  EXPECT_NE(result.find("int x = `PAIR(1,"), std::string::npos);
}

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

TEST(Preprocessor, DefineBodyLeavingAListOpenTakesNoFollowingLine) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define OPEN(a) `PAIR(a,\n"
      "int y;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\nint y;\n"), std::string::npos);
}

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

TEST(Preprocessor, UsageInsideATripleQuotedStringIsNotJoined) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define PAIR(a, b) a b\n"
      "string s = \"\"\"\n"
      "`PAIR(1,\n"
      "2)\"\"\";\n"
      "int y;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("`PAIR(1,\n2)\"\"\";\nint y;\n"), std::string::npos);
}

TEST(Preprocessor, LinesInsideAnOpenTripleQuotedStringPassThroughAsWritten) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M EXPANDED\n"
      "string s = \"\"\"first\n"
      "`M second\n"
      "`define X 1\n"
      "\"\"\";\n"
      "`ifdef X\n"
      "int defined_x;\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\"\"\"first\n`M second\n`define X 1\n\"\"\";\n"),
            std::string::npos);
  EXPECT_EQ(result.find("EXPANDED"), std::string::npos);
  EXPECT_EQ(result.find("defined_x"), std::string::npos);
}

TEST(Preprocessor, UsageAfterATripleQuotedStringClosesOnItsLastLineExpands) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M EXPANDED\n"
      "string s = \"\"\"first\n"
      "second\"\"\"; int x = `M;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("second\"\"\"; int x = EXPANDED;\n"),
            std::string::npos);
}

TEST(Preprocessor, DirectiveAfterATripleQuotedStringClosesOnItsLastLineActs) {
  PreprocFixture f;
  auto result = Preprocess(
      "string s = \"\"\"first\n"
      "second\"\"\"; `define Y 2\n"
      "int y = `Y;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int y = 2;"), std::string::npos);
  EXPECT_EQ(result.find("`define"), std::string::npos);
}

TEST(Preprocessor, UsageAfterALoneQuoteInATripleQuotedStringIsNotExpanded) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M EXPANDED\n"
      "string s = \"\"\"a\"b `M\"\"\";\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\"\"\"a\"b `M\"\"\";"), std::string::npos);
  EXPECT_EQ(result.find("EXPANDED"), std::string::npos);
}

TEST(Preprocessor, UsageAfterATripleQuotedStringHoldingALoneQuoteExpands) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M EXPANDED\n"
      "string s = \"\"\"a\"b\"\"\"; int x = `M;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = EXPANDED;"), std::string::npos);
}

TEST(Preprocessor, UsageAfterAStringEndingInAnEscapedBackslashExpands) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M EXPANDED\n"
      "string s = \"a\\\\\"; int x = `M;\n"
      "string t = \"\"\"b\\\\\"\"\"; int y = `M;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = EXPANDED;"), std::string::npos);
  EXPECT_NE(result.find("int y = EXPANDED;"), std::string::npos);
}

TEST(Preprocessor, QuoteOpeningAnEscapedIdentifierOpensNoString) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M EXPANDED\n"
      "logic \\\"q ; assign \\\"q = `M;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("assign \\\"q = EXPANDED;"), std::string::npos);
}

TEST(Preprocessor, UsageAfterAQuoteInsideAnEscapedIdentifierExpands) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M EXPANDED\n"
      "assign \\a\"b = `M;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("assign \\a\"b = EXPANDED;"), std::string::npos);
}

TEST(Preprocessor, DirectiveAfterAQuoteInsideAnEscapedIdentifierActs) {
  PreprocFixture f;
  auto result = Preprocess(
      "assign \\a\"b = 1; `define X 1\n"
      "`ifdef X\n"
      "int defined_x;\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int defined_x;"), std::string::npos);
}

TEST(Preprocessor, InlineConditionalAfterAQuoteInsideAnEscapedIdentifier) {
  PreprocFixture f;
  auto result =
      Preprocess("assign \\a\"b = `ifdef X one `else two `endif ;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("`ifdef"), std::string::npos);
  EXPECT_EQ(result.find("one"), std::string::npos);
  EXPECT_NE(result.find("two"), std::string::npos);
}

TEST(Preprocessor, UsageAfterAQuoteFollowingAUsageInAnEscapedIdentifier) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define B mid\n"
      "`define M EXPANDED\n"
      "assign \\a`B\"c = `M;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("assign \\amid\"c = EXPANDED;"), std::string::npos);
}

TEST(Preprocessor, DirectiveAfterAQuoteFollowingAUsageInAnEscapedIdentifier) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define B mid\n"
      "assign \\a`B\"c = 1; `define X 1\n"
      "`ifdef X\n"
      "int defined_x;\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int defined_x;"), std::string::npos);
}

TEST(Preprocessor, InlineConditionalAfterAQuoteFollowingAUsageInAnIdentifier) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define B mid\n"
      "assign \\a`B\"c = `ifdef X one `else two `endif ;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("`ifdef"), std::string::npos);
  EXPECT_EQ(result.find("one"), std::string::npos);
  EXPECT_NE(result.find("two"), std::string::npos);
}

TEST(Preprocessor, QuoteAfterAnEscapedIdentifierHoldingAUsageOpensAString) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define B mid\n"
      "`define M EXPANDED\n"
      "assign \\a`B = \"`M\";\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("assign \\amid = \"`M\";"), std::string::npos);
}

TEST(Preprocessor, DirectiveAfterALoneQuoteInATripleQuotedStringIsText) {
  PreprocFixture f;
  auto result = Preprocess(
      "string s = \"\"\"a\"b `define X 1\"\"\";\n"
      "`ifdef X\n"
      "int defined_x;\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\"\"\"a\"b `define X 1\"\"\";"), std::string::npos);
  EXPECT_EQ(result.find("defined_x"), std::string::npos);
}

TEST(Preprocessor,
     InlineConditionalAfterALoneQuoteInATripleQuotedStringIsText) {
  PreprocFixture f;
  auto result =
      Preprocess("string s = \"\"\"a\"b `ifdef X 1 `endif\"\"\";\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\"\"\"a\"b `ifdef X 1 `endif\"\"\";"),
            std::string::npos);
}

TEST(Preprocessor, LineAmongTheArgumentsOfAOneLineUsageIsAnArgument) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define AT(a, b) a b\n"
      "int x = `AT(1, `__LINE__);\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("int x = 1 2;"), std::string::npos);
}

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

TEST(Preprocessor, TripleQuotedArgumentKeepsItsRightParenthesis) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M(a, b) $display(a, b);\n"
      "`M(\"\"\"a) b\"\"\", 2)\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("$display(\"\"\"a) b\"\"\", 2);"), std::string::npos);
}

TEST(Preprocessor, EscapedIdentifierArgumentKeepsItsRightParenthesis) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define ID(x) x\n"
      "assign `ID(\\a)b ) = 1;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("assign \\a)b = 1;"), std::string::npos);
}

TEST(Preprocessor, TripleQuotedDefaultTextIsOneDefault) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define D(a = \"\"\"x,)y\"\"\") [a]\n"
      "`D()\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("[\"\"\"x,)y\"\"\"]"), std::string::npos);
}

TEST(Preprocessor, EscapedQuoteInsideAStringArgumentClosesNothing) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M(a, b) $display(a, b);\n"
      "`M(\"q\\\"x,y\", 1)\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("$display(\"q\\\"x,y\", 1);"), std::string::npos);
}

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

TEST(Preprocessor, CommaInsideAParenthesizedDefaultSeparatesNoArguments) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M(a = f(1, 2), b = 0) a + b\n"
      "x = `M(, 3);\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("x = f(1, 2) + 3;"), std::string::npos) << result;
}

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

TEST(Preprocessor, GraveAccentOpeningNoMacroQuoteOpensNoString) {
  for (const char* text : {"a`", "`\\xyz", "`\\`xy"}) {
    PreprocFixture f;
    Preprocess(std::string("`define M ") + text + "\n", f);
    EXPECT_FALSE(f.diag.HasErrors()) << text;
  }
}

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

TEST(Preprocessor, LineOpeningWithAStringKeepsLaterStringsUnexpanded) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define ONE 1\n"
      "\"a\" `ONE \"`ONE\" `ONE\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\"a\" 1 \"`ONE\" 1"), std::string::npos);
}

TEST(Preprocessor, EscapedQuoteBeforeAUsageClosesNoString) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define ONE 1\n"
      "x = \"a\\\"b\" `ONE \"`ONE\" `ONE\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("x = \"a\\\"b\" 1 \"`ONE\" 1"), std::string::npos);
}

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

TEST(Preprocessor, DefineMissingItsNameIsReported) {
  for (const char* directive :
       {"`define\n", "`define 5 x\n", "`define $x 1\n"}) {
    PreprocFixture f;
    Preprocess(directive, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "`define is missing its macro name", 1, "22.5.1"))
        << directive;
  }
}

TEST(Preprocessor, UnclosedFormalArgumentListIsReported) {
  PreprocFixture f;
  Preprocess("`define M(a, b\nx y\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "formal argument list of `define M is never closed",
                            1, "22.5.1"));
}

TEST(Preprocessor, UnterminatedBlockCommentInMacroTextIsReported) {
  PreprocFixture f;
  Preprocess("`define M a /* x", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "unterminated block comment",
                            1, "5.4"));
}

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
  auto line_of = [&out](const std::string& name) {
    size_t at = out.find(name + " =");
    return at == std::string::npos ? std::string("<missing>")
                                   : out.substr(at, out.find(';', at) - at);
  };
  EXPECT_NE(line_of("a").find("(10)*3"), std::string::npos) << out;
  EXPECT_NE(line_of("b").find('3'), std::string::npos) << out;
  EXPECT_EQ(line_of("c").find_first_of("24"), std::string::npos) << out;
}
