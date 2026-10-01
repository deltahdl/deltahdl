#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST_F(VerifyParseTest, CovergroupWithIff) {
  auto* unit = Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        coverpoint x iff (en);
      endgroup
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

// LRM 19.5: a coverpoint can carry an explicit set of named bins given by a
// covergroup_range_list.
TEST(CoverPointParsing, CoverpointWithExplicitBins) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg @(posedge clk);
        coverpoint addr {
          bins low = {0, 1, 2};
          bins high = {[8:15]};
        }
      endgroup
    endmodule
  )"));
}

// LRM 19.5: the default specification defines a bin that catches the values
// that do not lie within any of the defined bins.
TEST(CoverPointParsing, CoverpointWithDefaultBin) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg @(posedge clk);
        coverpoint addr {
          bins low = {0, 1};
          bins others = default;
        }
      endgroup
    endmodule
  )"));
}

// LRM 19.5: bins may be illegal_bins or ignore_bins; wildcard bins are also
// admitted by the grammar.
TEST(CoverPointParsing, CoverpointWithIllegalIgnoreWildcardBins) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg @(posedge clk);
        coverpoint addr {
          illegal_bins bad = {7};
          ignore_bins skip = {6};
          wildcard bins w = {3};
        }
      endgroup
    endmodule
  )"));
}

// LRM 19.5: a coverage point specifies an integral or real expression to be
// covered, not only a simple variable.
TEST(CoverPointParsing, CoverpointOverExpression) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg @(posedge clk);
        coverpoint (a + b);
      endgroup
    endmodule
  )"));
}

// LRM 19.5: a coverpoint may be labeled; the label becomes the name of the
// coverage point.
TEST(CoverPointParsing, LabeledCoverpoint) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg @(posedge clk);
        cp_addr: coverpoint addr;
      endgroup
    endmodule
  )"));
}

// LRM 19.5 (Syntax 19-2, covergroup_value_range): a value range may be
// open-ended using $ for the low or high bound.
TEST(CoverPointParsing, CoverpointWithOpenEndedRangeBins) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg @(posedge clk);
        coverpoint addr {
          bins lo = {[$:15]};
          bins hi = {[240:$]};
        }
      endgroup
    endmodule
  )"));
}

// LRM 19.5 (Syntax 19-2, covergroup_value_range): a value range may be written
// as a center with a +/- or +%- tolerance.
TEST(CoverPointParsing, CoverpointWithToleranceRangeBins) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg @(posedge clk);
        coverpoint addr {
          bins near = {[100 +/- 4]};
          bins pct  = {[100 +%- 10]};
        }
      endgroup
    endmodule
  )"));
}

// LRM 19.5 (Syntax 19-2, bins_or_options): the default sequence form catches
// transitions that do not lie within any defined transition bin.
TEST(CoverPointParsing, CoverpointWithDefaultSequenceBin) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg @(posedge clk);
        coverpoint addr {
          bins t = (0 => 1);
          bins others = default sequence;
        }
      endgroup
    endmodule
  )"));
}

// LRM 19.5 (Syntax 19-2, bins_or_options): a bin may be assigned a trans_list
// describing one or more value-transition sequences.
TEST(CoverPointParsing, CoverpointWithTransitionListBins) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg @(posedge clk);
        coverpoint addr {
          bins seq = (0 => 1 => 2);
        }
      endgroup
    endmodule
  )"));
}

// §19.5: an unlabelled coverpoint over a single variable takes the variable's
// name, and the clause's own example marks a label equal to that name as
// invalid; a later label differing from it, and a label naming the variable
// an earlier coverpoint covers under another name, are accepted.
TEST_F(VerifyParseTest, CoverpointLabelEqualToImplicitNameIsError) {
  Parse(R"(
    module m;
      covergroup cg (ref int x, ref int y, input int c);
        coverpoint x;
        x: coverpoint y;
        b: coverpoint y;
        cx: coverpoint x;
        option.weight = c;
      endgroup
    endmodule
  )");
  EXPECT_EQ(diag_.ErrorCount(), 1u);
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "the name 'x' already names a coverpoint or "
                            "cross of covergroup 'cg'",
                            5, "19.5"));
}

// §19.5 and §19.6: a coverpoint's name and a cross's name share the
// covergroup's scope, so two labels alike, or a cross label equal to a
// coverpoint's, each repeat a name already taken.
TEST_F(VerifyParseTest, RepeatedCoverpointOrCrossLabelIsError) {
  Parse(R"(
    module m;
      bit [1:0] v;
      bit [1:0] w;
      covergroup cg;
        a: coverpoint v;
        a: coverpoint w;
        b: coverpoint w;
        b: cross a, v;
      endgroup
    endmodule
  )");
  EXPECT_EQ(diag_.ErrorCount(), 2u);
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "the name 'a' already names a coverpoint or "
                            "cross of covergroup 'cg'",
                            7, "19.5"));
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "the name 'b' already names a coverpoint or "
                            "cross of covergroup 'cg'",
                            9, "19.5"));
}

}  // namespace
