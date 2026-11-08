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

TEST(CoverPointParsing, CoverpointOverExpression) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg @(posedge clk);
        coverpoint (a + b);
      endgroup
    endmodule
  )"));
}

TEST(CoverPointParsing, LabeledCoverpoint) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg @(posedge clk);
        cp_addr: coverpoint addr;
      endgroup
    endmodule
  )"));
}

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
