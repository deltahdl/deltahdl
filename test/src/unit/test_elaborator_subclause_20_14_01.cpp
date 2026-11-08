#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(RandomSeedType, IntegralSeedIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  integer seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RandomSeedType, IntSeedIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  int seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RandomSeedType, PackedVectorSeedIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  bit [31:0] seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RandomSeedType, ByteSeedIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  byte seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RandomSeedType, RealSeedIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  real seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$random cannot take its seed from a variable that is not integral", 4,
      "20.14.1"));
}

TEST(RandomSeedType, ShortrealSeedIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  shortreal seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$random cannot take its seed from a variable that is not integral", 4,
      "20.14.1"));
}

TEST(RandomSeedType, RealtimeSeedIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  realtime seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$random cannot take its seed from a variable that is not integral", 4,
      "20.14.1"));
}

TEST(RandomSeedType, StringSeedIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  string seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$random cannot take its seed from a variable that is not integral", 4,
      "20.14.1"));
}

TEST(RandomSeedType, SeedlessFormIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  integer x;\n"
      "  initial x = $random;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RandomSeedType, RealSeedInAForStepIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  real seed;\n"
      "  integer x;\n"
      "  integer i;\n"
      "  initial for (i = 0; i < 2; x = $random(seed)) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$random cannot take its seed from a variable that is not integral", 5,
      "20.14.1"));
}

TEST(RandomSeedType, RealSeedInAnAssertionPassStatementIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  real seed;\n"
      "  integer x;\n"
      "  logic ok;\n"
      "  initial assert (ok) x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$random cannot take its seed from a variable that is not integral", 5,
      "20.14.1"));
}

TEST(RandomSeedType, RealSeedInAnAssertionFailStatementIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  real seed;\n"
      "  integer x;\n"
      "  logic ok;\n"
      "  initial assert (ok) else x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$random cannot take its seed from a variable that is not integral", 5,
      "20.14.1"));
}

TEST(RandomSeedType, RealSeedInARandcaseItemIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  real seed;\n"
      "  integer x;\n"
      "  initial randcase 1: x = $random(seed); endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$random cannot take its seed from a variable that is not integral", 4,
      "20.14.1"));
}

TEST(RandomSeedType, RealSeedInARandsequenceCodeBlockIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  real seed;\n"
      "  integer x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { x = $random(seed); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$random cannot take its seed from a variable that is not integral", 6,
      "20.14.1"));
}

TEST(RandomSeedType, RealSeedInARandsequenceWeightCodeBlockIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  real seed;\n"
      "  integer x;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { x = $random(seed); };\n"
      "      alt : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$random cannot take its seed from a variable that is not integral", 7,
      "20.14.1"));
}

}  // namespace
