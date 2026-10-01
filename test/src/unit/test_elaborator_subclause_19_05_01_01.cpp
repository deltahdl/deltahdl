#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §19.5.1.1: a `with` expression filters the values of a bin, and is not
// allowed for the bins of a real coverpoint, whether it follows a range list
// or the coverpoint's own name. An integral coverpoint's bin may take one.
TEST(RealCoverpointBinWith, WithOnRealCoverpointBinIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  int i;\n"
      "  covergroup cg;\n"
      "    a: coverpoint r { bins b[] = {[1.0:4.0]} with (item > 2.0); }\n"
      "    c: coverpoint r { bins d = c with (item > 2.0); }\n"
      "    e: coverpoint i { bins g[] = {[1:4]} with (item > 2); }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  for (uint32_t line : {5u, 6u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "a bin of a real coverpoint takes no 'with' "
                              "expression",
                              line, "19.5.1.1"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

}  // namespace
