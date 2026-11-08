#include <gtest/gtest.h>

#include "elaborator/always_range.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AlwaysRange, BoundedNonNegativeRangeIsWellFormed) {
  AlwaysRange range{MakeAlwaysBound(0), MakeAlwaysBound(3)};
  EXPECT_TRUE(IsAlwaysRangeWellFormed(range, false));
}

TEST(AlwaysRange, EqualBoundsAreWellFormed) {
  AlwaysRange range{MakeAlwaysBound(2), MakeAlwaysBound(2)};
  EXPECT_TRUE(IsAlwaysRangeWellFormed(range, false));
}

TEST(AlwaysRange, WeakAlwaysAllowsUnboundedMaximum) {
  AlwaysRange range{MakeAlwaysBound(1), MakeAlwaysDollar()};
  EXPECT_TRUE(IsAlwaysRangeWellFormed(range, false));
}

TEST(AlwaysRange, StrongAlwaysRejectsUnboundedMaximum) {
  AlwaysRange range{MakeAlwaysBound(1), MakeAlwaysDollar()};
  EXPECT_FALSE(IsAlwaysRangeWellFormed(range, true));
}

TEST(AlwaysRange, StrongAlwaysAcceptsBoundedRange) {
  AlwaysRange range{MakeAlwaysBound(0), MakeAlwaysBound(4)};
  EXPECT_TRUE(IsAlwaysRangeWellFormed(range, true));
}

TEST(AlwaysRange, MinimumGreaterThanMaximumIsRejected) {
  AlwaysRange range{MakeAlwaysBound(5), MakeAlwaysBound(2)};
  EXPECT_FALSE(IsAlwaysRangeWellFormed(range, false));
}

TEST(AlwaysRange, NegativeMinimumIsRejected) {
  AlwaysRange range{MakeAlwaysBound(-1), MakeAlwaysBound(3)};
  EXPECT_FALSE(IsAlwaysRangeWellFormed(range, false));
}

TEST(AlwaysRange, NegativeMaximumIsRejected) {
  AlwaysRange range{MakeAlwaysBound(0), MakeAlwaysBound(-2)};
  EXPECT_FALSE(IsAlwaysRangeWellFormed(range, false));
}

TEST(AlwaysRange, NonConstantBoundIsRejected) {
  AlwaysRangeBound non_constant;
  non_constant.is_constant = false;
  non_constant.is_integer = true;
  non_constant.value = 2;
  AlwaysRange range{non_constant, MakeAlwaysBound(4)};
  EXPECT_FALSE(IsAlwaysRangeWellFormed(range, false));
}

TEST(AlwaysRange, NonIntegerBoundIsRejected) {
  AlwaysRangeBound non_integer;
  non_integer.is_constant = true;
  non_integer.is_integer = false;
  non_integer.value = 1;
  AlwaysRange range{MakeAlwaysBound(0), non_integer};
  EXPECT_FALSE(IsAlwaysRangeWellFormed(range, false));
}

TEST(AlwaysRangeElaboration, AParameterRangeIsChecked) {
  const char* const kReport =
      "always range bounds shall be non-negative integer constant "
      "expressions, the minimum no greater than the maximum";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a;\n"
      "  localparam int LO = 4, HI = 2;\n"
      "  a1: assert property (@(posedge clk) always [LO:HI] a);\n"
      "  a2: assert property (@(posedge clk) always [HI:LO] a);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 4, "16.12.11"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 5, "16.12.11"));
}

}  // namespace
