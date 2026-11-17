#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>

#include "elaborator/cross_bin_with_covergroup.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(CrossBinWithCovergroup, OnlyEnclosingCrossIdentifierIsLegal) {
  EXPECT_TRUE(CrossIdentifierSelectIsLegal("X", "X"));
  EXPECT_FALSE(CrossIdentifierSelectIsLegal("Y", "X"));
}

TEST(CrossBinWithCovergroup, MatchesCountShallBePositive) {
  EXPECT_TRUE(CrossMatchesCountIsLegal(1));
  EXPECT_TRUE(CrossMatchesCountIsLegal(127));
  EXPECT_FALSE(CrossMatchesCountIsLegal(0));
  EXPECT_FALSE(CrossMatchesCountIsLegal(-3));
}

TEST(CrossBinMatches, ConstantCountOfZeroOrLessIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [1:0] a, b;\n"
      "  covergroup cg;\n"
      "    coverpoint a;\n"
      "    coverpoint b;\n"
      "    X: cross a, b {\n"
      "      bins z = X with (a == b) matches 0;\n"
      "      bins n = X with (a < b) matches -1;\n"
      "      bins one = X with (a > b) matches 1;\n"
      "      bins all = X with (a != b) matches $;\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the matches count of bin 'z' is 0; it is a "
                            "positive integer or $",
                            7, "19.6.1.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the matches count of bin 'n' is -1; it is a "
                            "positive integer or $",
                            8, "19.6.1.2"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(CrossBinMatches, SelectingThroughAnotherCrossIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [1:0] a, b;\n"
      "  covergroup cg;\n"
      "    coverpoint a;\n"
      "    coverpoint b;\n"
      "    Y: cross a, b;\n"
      "    X: cross a, b {\n"
      "      bins eq = Y with (a == b);\n"
      "      bins own = X with (a == b);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bin 'eq' selects through cross 'Y'; only the "
                            "enclosing cross may be named there",
                            8, "19.6.1.2"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(CrossBinWithCovergroup, BareSelectThroughAnotherCrossIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [1:0] a, b;\n"
      "  covergroup cg;\n"
      "    coverpoint a; coverpoint b;\n"
      "    Y: cross a, b;\n"
      "    X: cross a, b { bins eq = Y; bins own = X; }\n"
      "    cross a, b { bins three = X; }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bin 'eq' selects through cross 'Y'; only the "
                            "enclosing cross may be named there",
                            6, "19.6.1.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bin 'three' selects through cross 'X'; only the "
                            "enclosing cross may be named there",
                            7, "19.6.1.2"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(CrossBinWithCovergroup, DISABLED_ANonIntegralWithExpressionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class K; endclass\n"
      "  bit [1:0] a, b;\n"
      "  parameter string ps = \"a\";\n"
      "  function automatic K mk(); return null; endfunction\n"
      "  covergroup cg;\n"
      "    coverpoint a; coverpoint b;\n"
      "    X: cross a, b {\n"
      "      bins s = X with (ps);\n"
      "      bins h = X with (mk());\n"
      "      bins bs = binsof(a) with (ps);\n"
      "      bins i = X with (a < b);\n"
      "      bins r = binsof(a) with (a * 1.5);\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  for (const auto& [name, line] :
       {std::pair<const char*, uint32_t>{"s", 9}, {"h", 10}, {"bs", 11}}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("the 'with' expression of bin '") +
                                  name +
                                  "' is not assignment compatible with an "
                                  "integral type",
                              line, "19.6"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

}  // namespace
