#include <gtest/gtest.h>

#include <string>

#include "common/types.h"
#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"

namespace {

class DirectivePlacement : public ::testing::Test {
 protected:
  std::string Run(const std::string& src) {
    auto fid = f_.mgr.AddFile("<test>", src);
    return pp_.Preprocess(fid);
  }

  bool TimescaleIs(TimeUnit unit, TimeUnit precision) const {
    return pp_.HasTimescale() && pp_.CurrentTimescale().unit == unit &&
           pp_.CurrentTimescale().precision == precision;
  }

  PreprocFixture f_;
  Preprocessor pp_{f_.mgr, f_.diag, {}};
};

TEST_F(DirectivePlacement, AnApostropheDoesNotOpenADirective) {
  Run("'define X 1\n`X\n");
  EXPECT_TRUE(
      ReportedError(f_.diag.Diagnostics(), "undefined macro 'X'", 2, "22.5.1"));
}

TEST_F(DirectivePlacement, AGraveAccentOpensTheSameDirective) {
  auto out = Run("`define X 1\nint v = `X;\n");
  EXPECT_FALSE(f_.diag.HasErrors());
  EXPECT_NE(out.find("int v = 1;"), std::string::npos) << out;
}

TEST_F(DirectivePlacement, ADirectiveInsideTimescaleIsRejected) {
  Run("`timescale 1ns `resetall / 1ps\n");
  EXPECT_TRUE(ReportedError(f_.diag.Diagnostics(), "invalid `timescale unit", 1,
                            "22.7"));
}

TEST_F(DirectivePlacement, ADirectiveInsideUnconnectedDriveIsRejected) {
  Run("`unconnected_drive `celldefine\n");
  EXPECT_TRUE(ReportedError(
      f_.diag.Diagnostics(),
      "invalid `unconnected_drive argument: '`celldefine'", 1, "22.9"));
}

TEST_F(DirectivePlacement, ADirectiveInsideIncludeIsRejected) {
  Run("`include `resetall \"x.svh\"\n");
  EXPECT_TRUE(ReportedError(
      f_.diag.Diagnostics(),
      "`include filename must be enclosed in double quotes or angle brackets",
      1, "22.4"));
}

TEST_F(DirectivePlacement, ADirectiveInsideUndefIsRejected) {
  Run("`define M 1\n`undef `resetall M\n");
  EXPECT_TRUE(ReportedError(f_.diag.Diagnostics(),
                            "`undef requires a text macro name", 2, "22.5.2"));
}

TEST_F(DirectivePlacement, ADirectiveInsideLineIsRejected) {
  Run("`line 10 `resetall \"f.sv\" 0\n");
  EXPECT_TRUE(ReportedError(f_.diag.Diagnostics(),
                            "`line directive requires a quoted filename", 1,
                            "22.12"));
}

TEST_F(DirectivePlacement, ADirectiveInsidePragmaIsRejected) {
  Run("`pragma `resetall name\n");
  EXPECT_TRUE(ReportedError(f_.diag.Diagnostics(),
                            "`pragma directive contains an illegal token", 1,
                            "22.11"));
}

TEST_F(DirectivePlacement, DISABLED_ADirectiveInsideBeginKeywordsIsRejected) {
  Run("`begin_keywords `resetall \"1800-2023\"\n`end_keywords\n");
  EXPECT_TRUE(ReportedError(
      f_.diag.Diagnostics(),
      "expected quoted version string after `begin_keywords", 1, "22.14"));
}

TEST_F(DirectivePlacement, StatementsMayPrecedeConditionalsOnOneLine) {
  auto out =
      Run("module m; initial begin a = 1; `ifdef X b = 1; `else c = 1; `endif "
          "d = 1; end endmodule\n");
  EXPECT_FALSE(f_.diag.HasErrors());
  EXPECT_NE(out.find("a = 1;"), std::string::npos) << out;
  EXPECT_EQ(out.find("b = 1;"), std::string::npos) << out;
  EXPECT_NE(out.find("c = 1;"), std::string::npos) << out;
  EXPECT_NE(out.find("d = 1;"), std::string::npos) << out;
}

TEST_F(DirectivePlacement, ATimescaleDoesNotTakeThePrecisionFromTheNextLine) {
  Run("`timescale 1ns\n/ 1ps\n");
  EXPECT_TRUE(ReportedError(f_.diag.Diagnostics(),
                            "invalid `timescale format: missing '/'", 1,
                            "22.7"));
  EXPECT_FALSE(pp_.HasTimescale());
}

TEST_F(DirectivePlacement, UnconnectedDriveDoesNotTakeTheNextLine) {
  auto out = Run("`unconnected_drive\npull1\n");
  EXPECT_TRUE(ReportedError(f_.diag.Diagnostics(),
                            "invalid `unconnected_drive argument: ''", 1,
                            "22.9"));
  EXPECT_NE(out.find("pull1"), std::string::npos) << out;
}

TEST_F(DirectivePlacement, IncludeDoesNotTakeTheNextLine) {
  auto out = Run("`include\n\"x.svh\"\n");
  EXPECT_TRUE(ReportedError(f_.diag.Diagnostics(),
                            "`include requires a filename", 1, "22.4"));
  EXPECT_NE(out.find("\"x.svh\""), std::string::npos) << out;
}

TEST_F(DirectivePlacement, UndefDoesNotTakeTheNextLine) {
  auto out = Run("`define M 1\n`undef\nM\n");
  EXPECT_TRUE(ReportedError(f_.diag.Diagnostics(),
                            "`undef requires a text macro name", 2, "22.5.2"));
  EXPECT_NE(out.find('M'), std::string::npos) << out;
}

TEST_F(DirectivePlacement, AMacroUsedInAnIgnoredBlockAppliesNoDirective) {
  Run("`define SET `timescale 1ns / 1ps\n"
      "`ifdef NOT_DEFINED\n"
      "`SET\n"
      "`endif\n");
  EXPECT_FALSE(f_.diag.HasErrors());
  EXPECT_FALSE(pp_.HasTimescale());
}

TEST_F(DirectivePlacement, ADirectiveCommentedAfterAnotherHasNoEffect) {
  Run("`timescale 1us / 1ns // `resetall\n");
  EXPECT_FALSE(f_.diag.HasErrors());
  EXPECT_TRUE(TimescaleIs(TimeUnit::kUs, TimeUnit::kNs));
}

TEST_F(DirectivePlacement, AMacroInDefineTextExpandsAtItsUse) {
  auto out =
      Run("`define A 1\n"
          "`define B `A\n"
          "`undef A\n"
          "`define A 2\n"
          "int v = `B;\n");
  EXPECT_FALSE(f_.diag.HasErrors());
  EXPECT_NE(out.find("int v = 2;"), std::string::npos) << out;
}

TEST_F(DirectivePlacement, DISABLED_AMacroInALineNumberIsExpanded) {
  Run("`define L 40\n`line `L \"f.sv\" 0\n");
  EXPECT_FALSE(f_.diag.HasErrors());
  EXPECT_TRUE(pp_.HasLineOverride());
  EXPECT_EQ(pp_.LineFile(), "f.sv");
}

TEST_F(DirectivePlacement, DISABLED_AMacroInAVersionSpecifierIsExpanded) {
  Run("`define B \"1800-2023\"\n`begin_keywords `B\n`end_keywords\n");
  EXPECT_FALSE(f_.diag.HasErrors());
}

TEST_F(DirectivePlacement, DISABLED_ATimescaleFollowsAnUndefOnItsLine) {
  Run("`define FOO 1\n`undef FOO `timescale 1us / 1ns\n");
  EXPECT_FALSE(f_.diag.HasErrors());
  EXPECT_TRUE(TimescaleIs(TimeUnit::kUs, TimeUnit::kNs));
}

TEST_F(DirectivePlacement, DISABLED_ADefaultNettypeFollowsAnUndefOnItsLine) {
  Run("`define FOO 1\n`undef FOO `default_nettype none\n");
  EXPECT_FALSE(f_.diag.HasErrors());
  EXPECT_EQ(pp_.DefaultNetType(), NetType::kNone);
}

TEST_F(DirectivePlacement, DISABLED_CodeHoldingConditionalsFollowsAResetall) {
  auto out =
      Run("`resetall module m; initial begin `ifdef FOO a = 1; `else b = 1; "
          "`endif end endmodule\n");
  EXPECT_FALSE(f_.diag.HasErrors());
  EXPECT_EQ(out.find("a = 1;"), std::string::npos) << out;
  EXPECT_NE(out.find("b = 1;"), std::string::npos) << out;
}

TEST_F(DirectivePlacement, DISABLED_CodeHoldingConditionalsFollowsATimescale) {
  auto out =
      Run("`timescale 1us / 1ns module m; initial begin `ifdef FOO a = 1; "
          "`else b = 1; `endif end endmodule\n");
  EXPECT_FALSE(f_.diag.HasErrors());
  EXPECT_TRUE(TimescaleIs(TimeUnit::kUs, TimeUnit::kNs));
  EXPECT_EQ(out.find("a = 1;"), std::string::npos) << out;
  EXPECT_NE(out.find("b = 1;"), std::string::npos) << out;
}

TEST_F(DirectivePlacement, DISABLED_AnElseAfterADirectiveOnASkippedLineIsSeen) {
  Run("`ifdef X\n"
      "`timescale 1us / 1ns `else\n"
      "`timescale 1ns / 1ps\n"
      "`endif\n");
  EXPECT_FALSE(f_.diag.HasErrors());
  EXPECT_TRUE(TimescaleIs(TimeUnit::kNs, TimeUnit::kPs));
}

}  // namespace
