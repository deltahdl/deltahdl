#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §19.5.1: a default bin of a real coverpoint catches every value no other bin
// holds as one bin; neither the `[]` nor the `[N]` array form is allowed for
// it. An integral coverpoint's default bin may be an array.
TEST(RealCoverpointDefaultBin, DefaultBinArrayOfRealCoverpointIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  int i;\n"
      "  covergroup cg;\n"
      "    a: coverpoint r { bins lo = {[0.0:1.0]}; bins d[] = default; }\n"
      "    b: coverpoint r { bins lo = {[0.0:1.0]}; bins e[4] = default; }\n"
      "    c: coverpoint r { bins lo = {[0.0:1.0]}; bins g = default; }\n"
      "    d: coverpoint i { bins h[] = default; }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  for (uint32_t line : {5u, 6u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "a real coverpoint's default bin is a single bin "
                              "and cannot be declared as an array",
                              line, "19.5.1"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

// §19.5.1: a fixed number of bins is given by a positive integral expression,
// so a constant count of zero or less is an error and a count of one is not.
TEST(FixedBinCount, ConstantCountOfZeroOrLessIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [3:0] v;\n"
      "  covergroup cg;\n"
      "    coverpoint v {\n"
      "      bins z[0] = {[0:7]};\n"
      "      bins n[-2] = {[8:15]};\n"
      "      bins one[1] = {[0:15]};\n"
      "    }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bins 'z' asks for 0 bins; the number of bins is a "
                            "positive integral value",
                            5, "19.5.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bins 'n' asks for -2 bins; the number of bins is "
                            "a positive integral value",
                            6, "19.5.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

}  // namespace
