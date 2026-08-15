#include "fixture_program.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST_F(VerifyParseTest, CovergroupWithCross) {
  auto* unit = Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        coverpoint a;
        coverpoint b;
        cross a, b;
      endgroup
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
}

// §19.6 / Syntax 19-4: list_of_cross_items requires at least two cross_items,
// so a one-item `cross a;` is rejected.
TEST_F(VerifyParseTest, SingleItemCrossIsError) {
  Parse(R"(
    module m;
      covergroup cg;
        coverpoint a;
        cross a;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "a cross shall list at least two coverage points",
                            5, "19.6"));
}

// §19.6: expressions cannot be used directly in a cross; a coverage point must
// be defined first, so `cross a + b, c;` is rejected.
TEST_F(VerifyParseTest, ExpressionCrossItemIsError) {
  Parse(R"(
    module m;
      covergroup cg;
        coverpoint a;
        coverpoint b;
        coverpoint c;
        cross a + b, c;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(
      diag_.Diagnostics(),
      "a cross item shall be a coverage point or variable identifier; "
      "an expression cannot be used directly in a cross",
      7, "19.6"));
}

// §19.6: the cross label is optional and, when present, precedes the
// two-or-more item list. A labeled two-item cross parses without error.
TEST_F(VerifyParseTest, LabeledCrossParsesWithoutError) {
  auto* unit = Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        coverpoint a;
        coverpoint b;
        axb : cross a, b;
      endgroup
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
}

// §19.6: a cross generalizes to more than two coverage points; a three-item
// cross with an `iff` guard parses without error.
TEST_F(VerifyParseTest, ThreeItemCrossWithIffParsesWithoutError) {
  auto* unit = Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        coverpoint a;
        coverpoint b;
        coverpoint c;
        cross a, b, c iff (enable);
      endgroup
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
}

}  // namespace
