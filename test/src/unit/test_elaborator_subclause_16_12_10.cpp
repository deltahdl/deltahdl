#include <gtest/gtest.h>

#include "elaborator/nexttime_index.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §16.12.10: the number of clock ticks given by the index constant_expression
// shall be a non-negative integer constant expression. A folded non-negative
// integer constant — including zero, the alignment-operator case — is
// well-formed.
TEST(NexttimeIndex, NonNegativeConstantIsWellFormed) {
  EXPECT_TRUE(IsNexttimeIndexWellFormed(MakeNexttimeIndex(0)));
  EXPECT_TRUE(IsNexttimeIndexWellFormed(MakeNexttimeIndex(1)));
  EXPECT_TRUE(IsNexttimeIndexWellFormed(MakeNexttimeIndex(7)));
}

// §16.12.10: the count of clock ticks shall be non-negative, so a negative
// index is rejected.
TEST(NexttimeIndex, NegativeConstantIsRejected) {
  EXPECT_FALSE(IsNexttimeIndexWellFormed(MakeNexttimeIndex(-1)));
}

// §16.12.10: the index shall be a constant expression. An index that does not
// fold to a compile-time constant is rejected even though its recorded value
// would be a non-negative integer.
TEST(NexttimeIndex, NonConstantIsRejected) {
  NexttimeIndex index;
  index.is_constant = false;
  index.is_integer = true;
  index.value = 2;
  EXPECT_FALSE(IsNexttimeIndexWellFormed(index));
}

// §16.12.10: the index shall be an integer. A constant that is not an integer
// value is rejected.
TEST(NexttimeIndex, NonIntegerConstantIsRejected) {
  NexttimeIndex index;
  index.is_constant = true;
  index.is_integer = false;
  index.value = 0;
  EXPECT_FALSE(IsNexttimeIndexWellFormed(index));
}

// §16.12.10: a nexttime index written as a parameter is a non-negative
// integer constant: NEG folds to -1, k to no constant, and ONE to 1.
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
