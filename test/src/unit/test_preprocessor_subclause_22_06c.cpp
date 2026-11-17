#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

bool Holds(const std::string& out, const std::string& text) {
  return out.find(text) != std::string::npos;
}

bool ErrorAt(const PreprocFixture& f, const std::string& message,
             uint32_t line) {
  for (const auto& d : f.diag.Diagnostics()) {
    if (d.loc.line == line && d.message.find(message) != std::string::npos) {
      return true;
    }
  }
  return false;
}

TEST(ConditionalDirectiveNames, IfndefOfADirectiveNameTakesItsGroup) {
  for (const char* name : {"define", "timescale", "endif"}) {
    PreprocFixture f;
    auto out = Preprocess(std::string("`ifndef ") + name +
                              "\ntaken_group\n`else\nother_group\n`endif\n",
                          f);
    EXPECT_FALSE(f.diag.HasErrors()) << name;
    EXPECT_TRUE(Holds(out, "taken_group")) << name << out;
    EXPECT_FALSE(Holds(out, "other_group")) << name << out;
  }
}

TEST(ConditionalDirectiveNames, ADirectiveNameOperandCountsAsUndefined) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define B\n"
      "`ifdef (define || A)\nor_group\n`endif\n"
      "`ifndef (endif && B)\nand_group\n`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Holds(out, "or_group")) << out;
  EXPECT_TRUE(Holds(out, "and_group")) << out;
}

TEST(ConditionalGroups, OnlyTheFirstSucceedingElsifIsCompiled) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define B\n`define C\n"
      "`ifdef A\na_group\n`elsif B\nb_group\n`elsif C\nc_group\n`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Holds(out, "a_group")) << out;
  EXPECT_TRUE(Holds(out, "b_group")) << out;
  EXPECT_FALSE(Holds(out, "c_group")) << out;
}

TEST(ConditionalGroups, AnUndefInAnIgnoredBlockLeavesTheMacroDefined) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define M\n`ifdef NOPE\n`undef M\n`endif\n"
      "`ifdef M\nstill_defined\n`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(out, "still_defined")) << out;
}

TEST(ConditionalMacroNames, AnEscapedNameSelectsItsGroup) {
  PreprocFixture f;
  auto out =
      Preprocess("`define \\M@C \n`ifdef \\M@C \nescaped_group\n`endif\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(out, "escaped_group")) << out;
}

TEST(ConditionalMacroNames, ANameWithDollarAndDigitsSelectsItsGroup) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define A$1\n"
      "`ifdef A$1\nifdef_group\n`endif\n"
      "`ifndef A$1\nifndef_group\n`endif\n"
      "`ifdef Z\n`elsif A$1\nelsif_group\n`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(out, "ifdef_group")) << out;
  EXPECT_FALSE(Holds(out, "ifndef_group")) << out;
  EXPECT_TRUE(Holds(out, "elsif_group")) << out;
}

TEST(ConditionalMacroNames, DISABLED_ANumberAsTheConditionIsReported) {
  PreprocFixture f;
  Preprocess("`ifdef 123\nx\n`endif\n", f);
  bool reported = false;
  for (const auto& d : f.diag.Diagnostics()) {
    reported = reported || (d.loc.line == 1 && d.subclause == "22.6");
  }
  EXPECT_TRUE(reported);
}

TEST(ConditionalMacroNames, AnIdentifierStartingWithALetterIsAccepted) {
  PreprocFixture f;
  Preprocess("`ifdef N123\nx\n`endif\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConditionalPrecedence, AndBindsTighterThanOr) {
  PreprocFixture only_a;
  auto out_a =
      Preprocess("`define A\n`ifdef (B || A && C)\ngroup\n`endif\n", only_a);
  EXPECT_FALSE(Holds(out_a, "group")) << out_a;
  PreprocFixture only_b;
  auto out_b =
      Preprocess("`define B\n`ifdef (B || A && C)\ngroup\n`endif\n", only_b);
  EXPECT_TRUE(Holds(out_b, "group")) << out_b;
}

TEST(ConditionalPrecedence, NotBindsTighterThanAnd) {
  PreprocFixture only_a;
  auto out_a =
      Preprocess("`define A\n`ifdef (!B && A)\ngroup\n`endif\n", only_a);
  EXPECT_TRUE(Holds(out_a, "group")) << out_a;
  PreprocFixture both;
  auto out_both = Preprocess(
      "`define A\n`define B\n`ifdef (!B && A)\ngroup\n`endif\n", both);
  EXPECT_FALSE(Holds(out_both, "group")) << out_both;
}

TEST(ConditionalIfndef, AFailedIfndefFallsToTheFirstDefinedElsif) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define X\n`define E2\n"
      "`ifndef X\ng1\n`elsif E1\ng2\n`elsif E2\ng3\n`else\ng4\n`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Holds(out, "g1")) << out;
  EXPECT_FALSE(Holds(out, "g2")) << out;
  EXPECT_TRUE(Holds(out, "g3")) << out;
  EXPECT_FALSE(Holds(out, "g4")) << out;
}

TEST(ConditionalIfndef, TheElseGroupIsTakenWhenNoElsifIsSelected) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define X\n"
      "`ifndef X\ng1\n`elsif E1\ng2\n`elsif E2\ng3\n`else\ng4\n`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(Holds(out, "g3")) << out;
  EXPECT_TRUE(Holds(out, "g4")) << out;
}

TEST(ConditionalForm, AnInlineElsifGroupOnASourceLine) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define B\nx = `ifdef A 11 `elsif B 22 `else 33 `endif ;\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(out, "22")) << out;
  EXPECT_FALSE(Holds(out, "11")) << out;
  EXPECT_FALSE(Holds(out, "33")) << out;
}

TEST(ConditionalForm, AnUnclosedIfndefIsReported) {
  PreprocFixture f;
  Preprocess("`ifndef A\nx\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`ifdef or `ifndef with no closing `endif", 1,
                            "22.6"));
}

TEST(ConditionalForm, AnOuterIfdefLeftOpenAroundAClosedInnerIsReported) {
  PreprocFixture f;
  Preprocess("`ifdef A\n`ifdef B\n`endif\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`ifdef or `ifndef with no closing `endif", 1,
                            "22.6"));
}

TEST(ConditionalForm, DISABLED_AnElsifAfterTheElseIsReported) {
  PreprocFixture f;
  Preprocess("`ifdef A\n`else\n`elsif B\n`endif\n", f);
  bool reported = false;
  for (const auto& d : f.diag.Diagnostics()) {
    reported = reported || (d.loc.line == 3 && d.subclause == "22.6");
  }
  EXPECT_TRUE(reported);
}

TEST(ConditionalForm, AnElsifBeforeTheElseIsAccepted) {
  PreprocFixture f;
  Preprocess("`ifdef A\n`elsif B\n`else\n`endif\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConditionalWhiteSpace, NoBlanksAroundOrInsideTheExpression) {
  PreprocFixture f;
  auto out = Preprocess("`define A\n`ifdef(A&&!B)\ntight_group\n`endif\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(out, "tight_group")) << out;
}

TEST(ConditionalWhiteSpace, CommentsAfterTheDirectivesChangeNothing) {
  PreprocFixture f;
  auto out = Preprocess(
      "`define A\n"
      "`ifdef A // c\nfirst_group\n`else /* c */\nsecond_group\n"
      "`endif // c\nafter_block\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(out, "first_group")) << out;
  EXPECT_FALSE(Holds(out, "second_group")) << out;
  EXPECT_TRUE(Holds(out, "after_block")) << out;
}

TEST(IgnoredBlockLexing, DISABLED_AnUnterminatedBlockCommentIsReported) {
  PreprocFixture f;
  Preprocess("`ifdef NOT_DEFINED\n/* open\n`endif\n", f);
  EXPECT_TRUE(ErrorAt(f, "unterminated block comment", 2));
}

TEST(IgnoredBlockLexing, AnIllegalCharacterIsReported) {
  PreprocFixture f;
  Preprocess(std::string("`ifdef NOT_DEFINED\nx \x01 y\n`endif\n"), f);
  EXPECT_TRUE(ErrorAt(f, "unexpected character 0x01", 2));
}

}  // namespace
