#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_program.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST_F(VerifyParseTest, TransitionOfLengthZeroIsError) {
  Parse(R"(
    module m;
      bit [1:0] v;
      covergroup cg;
        coverpoint v {
          bins z = (0);
          bins r = ([0:1]);
          bins one = (0 [* 1]);
          bins span = (0 [* 1:1]);
          bins two = (0 => 1);
          bins rep = (3 [* 2]);
        }
      endgroup
    endmodule
  )");
  EXPECT_EQ(diag_.ErrorCount(), 4u);
  for (uint32_t line : {6u, 7u, 8u, 9u}) {
    EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                              "a transition of length 0 is illegal; its "
                              "trans_set covers a single value range",
                              line, "19.5.2"));
  }
}

TEST_F(VerifyParseTest, UnboundedTransitionInBinArrayIsError) {
  Parse(R"(
    module m;
      bit [2:0] v;
      covergroup cg;
        coverpoint v {
          bins a[] = (3 [= 2]);
          bins b[] = (1 => 3 [-> 2] => 5);
          bins c = (3 [= 2]);
          bins d = (1 => 3 [-> 2] => 5);
          bins e[] = (3 [* 2:4]);
        }
      endgroup
    endmodule
  )");
  EXPECT_EQ(diag_.ErrorCount(), 2u);
  for (uint32_t line : {6u, 7u}) {
    EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                              "a transition bin array '[ ]' cannot hold a "
                              "transition of unbounded length",
                              line, "19.5.2"));
  }
}

}  // namespace
