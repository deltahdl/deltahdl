#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_program.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST_F(VerifyParseTest, IgnoredTransitionOfUnboundedLengthIsError) {
  Parse(R"(
    module m;
      bit [2:0] v;
      covergroup cg;
        coverpoint v {
          bins t = (1 => 3 [-> 2]);
          ignore_bins a = (1 => 3 [-> 2]);
          ignore_bins b = (3 [= 2] => 5);
          ignore_bins c = (3 [* 2:4]);
          ignore_bins d = (1 => 2 => 3);
        }
      endgroup
    endmodule
  )");
  for (uint32_t line : {7u, 8u}) {
    EXPECT_TRUE(
        ReportedError(diag_.Diagnostics(),
                      "an ignore_bins transition cannot be of unbounded or "
                      "undetermined length",
                      line, "19.5.5"));
  }
  EXPECT_EQ(diag_.ErrorCount(), 2u);
}

}  // namespace
