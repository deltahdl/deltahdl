// §3.14.2: Specifying time units and precision

#include <gtest/gtest.h>

#include "fixture_preprocessor_timescale.h"

using namespace delta;

namespace {

// 29. Both mechanisms handle all three magnitudes (1, 10, 100).
TEST(ParserClause03, Cl3_14_2_BothMechanismsMagnitudes) {
  // `timescale with magnitudes.
  auto r1 = PreprocessTimescale("`timescale 1ns / 1ps\n");
  EXPECT_EQ(r1.timescale.magnitude, 1);
  auto r10 = PreprocessTimescale("`timescale 10ns / 10ps\n");
  EXPECT_EQ(r10.timescale.magnitude, 10);
  auto r100 = PreprocessTimescale("`timescale 100ns / 100ps\n");
  EXPECT_EQ(r100.timescale.magnitude, 100);
  // timeunit with magnitudes: all three parse successfully.
  EXPECT_FALSE(ParseTimescale31402("module m; timeunit 1ns; endmodule\n").has_errors);
  EXPECT_FALSE(ParseTimescale31402("module m; timeunit 10ns; endmodule\n").has_errors);
  EXPECT_FALSE(ParseTimescale31402("module m; timeunit 100ns; endmodule\n").has_errors);
}

}  // namespace
