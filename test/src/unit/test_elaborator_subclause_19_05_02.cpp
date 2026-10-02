#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §19.5.2: a trans_list orders transitions of integral values, and transition
// bins of real values are not allowed, whatever the bins keyword. An integral
// coverpoint's transition bins stay legal.
TEST(RealCoverpointTransitionBin, TransitionBinOfRealCoverpointIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  bit [1:0] x;\n"
      "  covergroup cg;\n"
      "    a: coverpoint r { bins one = {[1.0:2.0]}; bins t = (1.0 => 2.0); }\n"
      "    b: coverpoint r { bins one = {[1.0:2.0]};\n"
      "                      ignore_bins u = (2.0 => 3.0); }\n"
      "    c: coverpoint x { bins t = (1 => 2); }\n"
      "  endgroup\n"
      "  cg cv = new;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {5u, 7u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "a coverpoint of a real expression takes no "
                              "transition bin",
                              line, "19.5.2"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

}  // namespace
