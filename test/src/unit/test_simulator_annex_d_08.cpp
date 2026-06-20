#include "helpers_scheduler.h"

using namespace delta;

namespace {

// Annex D.8: $reset_count reports how many times $reset has run. Each $reset
// invocation tallies one more reset.
TEST(OptionalResetFamilySim, ResetCountTracksInvocations) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  integer c;\n"
                      "  initial begin\n"
                      "    $reset(1);\n"
                      "    $reset(1);\n"
                      "    $reset(1);\n"
                      "    c = $reset_count;\n"
                      "  end\n"
                      "endmodule\n",
                      "c"),
            3u);
}

// Annex D.8: with no $reset performed, $reset_count reads zero.
TEST(OptionalResetFamilySim, ResetCountStartsAtZero) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  integer c;\n"
                      "  initial c = $reset_count;\n"
                      "endmodule\n",
                      "c"),
            0u);
}

// Annex D.8: the reset_value argument to $reset (the second argument, after
// stop_value) is the value that $reset_value returns after the reset.
TEST(OptionalResetFamilySim, ResetValueReturnsResetArgument) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  integer v;\n"
                      "  initial begin\n"
                      "    $reset(1, 42);\n"
                      "    v = $reset_value;\n"
                      "  end\n"
                      "endmodule\n",
                      "v"),
            42u);
}

// Annex D.8: $reset_value reflects the most recent reset_value argument.
TEST(OptionalResetFamilySim, ResetValueTracksLatestReset) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  integer v;\n"
                      "  initial begin\n"
                      "    $reset(1, 7);\n"
                      "    $reset(1, 99);\n"
                      "    v = $reset_value;\n"
                      "  end\n"
                      "endmodule\n",
                      "v"),
            99u);
}

// Annex D.8 edge case: $reset with no argument list still counts as a reset.
TEST(OptionalResetFamilySim, ResetCountIncrementsWithoutArguments) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  integer c;\n"
                      "  initial begin\n"
                      "    $reset;\n"
                      "    c = $reset_count;\n"
                      "  end\n"
                      "endmodule\n",
                      "c"),
            1u);
}

// Annex D.8 edge case: with no reset performed, $reset_value reads its initial
// zero rather than an arbitrary leftover.
TEST(OptionalResetFamilySim, ResetValueDefaultsToZeroBeforeReset) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  integer v;\n"
                      "  initial v = $reset_value;\n"
                      "endmodule\n",
                      "v"),
            0u);
}

// Annex D.8 edge case: a $reset that supplies only stop_value carries no
// reset_value, so $reset_value stays at zero.
TEST(OptionalResetFamilySim, ResetValueZeroWhenResetValueOmitted) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  integer v;\n"
                      "  initial begin\n"
                      "    $reset(1);\n"
                      "    v = $reset_value;\n"
                      "  end\n"
                      "endmodule\n",
                      "v"),
            0u);
}

}  // namespace
