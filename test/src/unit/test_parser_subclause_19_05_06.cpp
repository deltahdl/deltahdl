#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_program.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST_F(VerifyParseTest, IllegalTransitionOfUnboundedLengthIsError) {
  Parse(R"(
    module m;
      bit [2:0] v;
      covergroup cg;
        coverpoint v {
          bins t = (1 => 3 [-> 2]);
          illegal_bins a = (1 => 3 [-> 2]);
          illegal_bins b = (3 [= 2] => 5);
          illegal_bins c = (3 [* 2:4]);
          illegal_bins d = (1 => 2 => 3);
        }
      endgroup
    endmodule
  )");
  for (uint32_t line : {7u, 8u}) {
    EXPECT_TRUE(
        ReportedError(diag_.Diagnostics(),
                      "an illegal_bins transition cannot be of unbounded or "
                      "undetermined length",
                      line, "19.5.6"));
  }
  EXPECT_EQ(diag_.ErrorCount(), 2u);
}

}  // namespace
