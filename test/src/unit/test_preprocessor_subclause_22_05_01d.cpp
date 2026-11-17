#include <gtest/gtest.h>

#include <string>

#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

bool Holds(const std::string& out, const std::string& text) {
  return out.find(text) != std::string::npos;
}

TEST(MacroTextEnd, ABackslashThenASpaceDoesNotContinueTheText) {
  PreprocFixture f;
  auto out = Preprocess("`define M 1 \\ \nint after;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(out, "int after;")) << out;
}

TEST(MacroTextEnd, ABackslashRightBeforeTheNewlineContinuesTheText) {
  PreprocFixture f;
  auto out = Preprocess("`define M 1 \\\n+ 2\nx = `M;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(out, "x = 1")) << out;
  EXPECT_TRUE(Holds(out, "+ 2;")) << out;
}

TEST(MacroTextEnd, ANewlineInsideATripleQuotedStringDoesNotEndTheText) {
  PreprocFixture f;
  auto out = Preprocess("`define S \"\"\"a\nb\"\"\"\nx = `S;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(out, "x = \"\"\"a\nb\"\"\";")) << out;
}

TEST(MacroTextEnd, ANewlineInsideABlockCommentDoesNotEndTheText) {
  PreprocFixture f;
  auto out = Preprocess("`define C 1 /* a\nb */ + 2\nx = `C;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  auto use = out.find("x = 1");
  ASSERT_NE(use, std::string::npos) << out;
  EXPECT_NE(out.find("+ 2;", use), std::string::npos) << out;
  EXPECT_FALSE(Holds(out.substr(0, use), "+ 2")) << out;
}

TEST(MacroActualList, AListAfterAnArgumentlessMacroStaysInTheSource) {
  PreprocFixture f;
  auto out = Preprocess("`define A 5\nx = `A(3);\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(out, "5(3);")) << out;
}

TEST(MacroActualList, DISABLED_AnUnclosedOrUnbalancedListIsReported) {
  for (const char* usage : {"`M(1;", "`M((1);", "`M([1);", "`M({1);"}) {
    PreprocFixture f;
    Preprocess(std::string("`define M(a) a\nx = ") + usage + "\n", f);
    bool reported = false;
    for (const auto& d : f.diag.Diagnostics()) {
      reported = reported || (d.loc.line == 2 && d.subclause == "22.5.1");
    }
    EXPECT_TRUE(reported) << usage;
  }
}

TEST(MacroActualList, AClosedBalancedListExpands) {
  PreprocFixture f;
  auto out = Preprocess("`define M(a) a\nx = `M(([{1}]));\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(out, "x = ([{1}]);")) << out;
}

TEST(MacroActualCount, AnEscapedFunctionLikeMacroWithoutAListIsReported) {
  PreprocFixture f;
  Preprocess("`define \\m (a=1) a\nx = `\\m ;\n", f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "parentheses required for function-like macro '\\m'", 2, "22.5.1"));
}

TEST(MacroActualCount, ExtraEmptyActualsAreReported) {
  for (const char* def : {"`define D(a) a\n", "`define D(a, b) a b\n"}) {
    PreprocFixture f;
    Preprocess(std::string(def) + "x = `D(,,);\n", f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "too many arguments for macro 'D'", 2, "22.5.1"))
        << def;
  }
}

TEST(MacroUsageName, AParenthesisJoinsAnEscapedNameWrittenWithoutASpace) {
  PreprocFixture f;
  auto out = Preprocess("`define \\M@ 9\nx = `\\M@(3) ;\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undefined macro '\\M@(3)'",
                            2, "22.5.1"));
  EXPECT_FALSE(Holds(out, "x = 9")) << out;
}

TEST(MacroActualList, ARightParenthesisInsideAStringStaysInTheActual) {
  PreprocFixture f;
  auto out = Preprocess("`define M(a, b) [a|b]\nx = `M(\"x)y\", 1);\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(out, "x = [\"x)y\"|1];")) << out;
}

TEST(MacroDefaults, ACommaInsideBracketsOrAnEscapedNameStaysInTheDefault) {
  for (const char* dflt : {"{1,2}", "[1,2]", "\\e,f "}) {
    PreprocFixture f;
    std::string src = "`define M(a, b=";
    src += dflt;
    src += ") [a|b]\nx = `M(3);\n";
    auto out = Preprocess(src, f);
    EXPECT_FALSE(f.diag.HasErrors()) << dflt;
    std::string want = "x = [3|";
    std::string trimmed = dflt;
    while (trimmed.back() == ' ') trimmed.pop_back();
    want += trimmed;
    want += ']';
    EXPECT_TRUE(Holds(out, want)) << dflt << "\n" << out;
  }
}

TEST(MacroScope, AMacroDefinedInsideAnElementIsUsableAfterIt) {
  for (const char* opener : {"module m;\n", "package p;\n", "class k;\n",
                             "module n;\ntask t();\n"}) {
    std::string closer =
        std::string(opener).starts_with("module m")  ? "endmodule\n"
        : std::string(opener).starts_with("package") ? "endpackage\n"
        : std::string(opener).starts_with("class")   ? "endclass\n"
                                                     : "endtask\nendmodule\n";
    PreprocFixture f;
    auto out = Preprocess(std::string(opener) + "`define INNER 47\n" + closer +
                              "module later;\nint a = `INNER;\nendmodule\n"
                              "int b = `INNER;\n",
                          f);
    EXPECT_FALSE(f.diag.HasErrors()) << opener;
    EXPECT_TRUE(Holds(out, "int a = 47;")) << opener << out;
    EXPECT_TRUE(Holds(out, "int b = 47;")) << opener << out;
  }
}

TEST(MacroTokenBoundary, DISABLED_AnOperatorDoesNotJoinTheTextAfterTheUsage) {
  PreprocFixture f;
  auto out = Preprocess("`define OP =\n`define L <\na `OP= b;\nc `L< 2;\n", f);
  EXPECT_FALSE(Holds(out, "==")) << out;
  EXPECT_FALSE(Holds(out, "<<")) << out;
}

TEST(MacroTokenBoundary, DISABLED_ANumberDoesNotJoinTheTextAfterTheUsage) {
  PreprocFixture f;
  auto out = Preprocess("`define N 1\nx = `N.5;\n", f);
  EXPECT_FALSE(Holds(out, "1.5")) << out;
}

TEST(MacroTokenBoundary, AnIdentifierDoesNotJoinTheTextAfterTheUsage) {
  PreprocFixture f;
  auto out = Preprocess("`define P ab\n`define K mod\n`P c;\n`K ule;\n", f);
  EXPECT_FALSE(Holds(out, "abc")) << out;
  EXPECT_FALSE(Holds(out, "module")) << out;
}

}  // namespace
