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
                              "a default bin of a real coverpoint shall not "
                              "be an array of bins",
                              line, "19.5.1"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

}  // namespace
