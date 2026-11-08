#include <gtest/gtest.h>

#include "elaborator/nexttime_index.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(NexttimeIndex, NonNegativeConstantIsWellFormed) {
  EXPECT_TRUE(IsNexttimeIndexWellFormed(MakeNexttimeIndex(0)));
  EXPECT_TRUE(IsNexttimeIndexWellFormed(MakeNexttimeIndex(1)));
  EXPECT_TRUE(IsNexttimeIndexWellFormed(MakeNexttimeIndex(7)));
}

TEST(NexttimeIndex, NegativeConstantIsRejected) {
  EXPECT_FALSE(IsNexttimeIndexWellFormed(MakeNexttimeIndex(-1)));
}

TEST(NexttimeIndex, NonConstantIsRejected) {
  NexttimeIndex index;
  index.is_constant = false;
  index.is_integer = true;
  index.value = 2;
  EXPECT_FALSE(IsNexttimeIndexWellFormed(index));
}

TEST(NexttimeIndex, NonIntegerConstantIsRejected) {
  NexttimeIndex index;
  index.is_constant = true;
  index.is_integer = false;
  index.value = 0;
  EXPECT_FALSE(IsNexttimeIndexWellFormed(index));
}

TEST(NexttimeIndexElaboration, AParameterIndexIsChecked) {
  const char* const kReport =
      "the index of nexttime shall be a non-negative integer constant "
      "expression";
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit clk, a;\n"
      "  int k;\n"
      "  localparam int NEG = -1, ONE = 1;\n"
      "  a1: assert property (@(posedge clk) nexttime [NEG] a);\n"
      "  a2: assert property (@(posedge clk) s_nexttime [k] a);\n"
      "  a3: assert property (@(posedge clk) nexttime [ONE] a);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 5, "16.12.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport, 6, "16.12.10"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport, 7, "16.12.10"));
}

}  // namespace
