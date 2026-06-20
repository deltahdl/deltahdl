#include "fixture_parser.h"
#include "fixture_program.h"

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

}  // namespace
