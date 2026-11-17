#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(DistributionArguments, UniformWithItsArgumentsIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_uniform(s, 0, 10);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(DistributionArguments, DISABLED_UniformWithTooFewArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_uniform(s, 0);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dist_uniform takes exactly 3 arguments", 3,
                            "20.14.2"));
}

TEST(DistributionArguments, DISABLED_UniformWithTooManyArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_uniform(s, 0, 10, 1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dist_uniform takes exactly 3 arguments", 3,
                            "20.14.2"));
}

TEST(DistributionArguments, DISABLED_UniformWithNoArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_uniform();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dist_uniform takes exactly 3 arguments", 3,
                            "20.14.2"));
}

TEST(DistributionSeed, DISABLED_AUniformLiteralSeedIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_uniform(5, 0, 10);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the seed of $dist_uniform shall be a variable it can write back", 3,
      "20.14.2"));
}

TEST(DistributionArguments, NormalWithItsArgumentsIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_normal(s, 0, 10);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(DistributionArguments, DISABLED_NormalWithTooFewArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_normal(s, 0);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dist_normal takes exactly 3 arguments", 3,
                            "20.14.2"));
}

TEST(DistributionArguments, DISABLED_NormalWithTooManyArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_normal(s, 0, 10, 1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dist_normal takes exactly 3 arguments", 3,
                            "20.14.2"));
}

TEST(DistributionArguments, DISABLED_NormalWithNoArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_normal();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dist_normal takes exactly 3 arguments", 3,
                            "20.14.2"));
}

TEST(DistributionSeed, DISABLED_ANormalLiteralSeedIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_normal(5, 0, 10);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the seed of $dist_normal shall be a variable it can write back", 3,
      "20.14.2"));
}

TEST(DistributionArguments, ExponentialWithItsArgumentsIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_exponential(s, 5);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(DistributionArguments, DISABLED_ExponentialWithTooFewArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_exponential(s);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dist_exponential takes exactly 2 arguments", 3,
                            "20.14.2"));
}

TEST(DistributionArguments,
     DISABLED_ExponentialWithTooManyArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_exponential(s, 5, 1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dist_exponential takes exactly 2 arguments", 3,
                            "20.14.2"));
}

TEST(DistributionArguments, DISABLED_ExponentialWithNoArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_exponential();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dist_exponential takes exactly 2 arguments", 3,
                            "20.14.2"));
}

TEST(DistributionSeed, DISABLED_AnExponentialLiteralSeedIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_exponential(5, 5);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the seed of $dist_exponential shall be a variable it can write back", 3,
      "20.14.2"));
}

TEST(DistributionArguments, PoissonWithItsArgumentsIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_poisson(s, 5);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(DistributionArguments, DISABLED_PoissonWithTooFewArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_poisson(s);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dist_poisson takes exactly 2 arguments", 3,
                            "20.14.2"));
}

TEST(DistributionArguments, DISABLED_PoissonWithTooManyArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_poisson(s, 5, 1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dist_poisson takes exactly 2 arguments", 3,
                            "20.14.2"));
}

TEST(DistributionArguments, DISABLED_PoissonWithNoArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_poisson();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dist_poisson takes exactly 2 arguments", 3,
                            "20.14.2"));
}

TEST(DistributionSeed, DISABLED_APoissonLiteralSeedIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_poisson(5, 5);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the seed of $dist_poisson shall be a variable it can write back", 3,
      "20.14.2"));
}

TEST(DistributionArguments, ChiSquareWithItsArgumentsIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_chi_square(s, 3);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(DistributionArguments, DISABLED_ChiSquareWithTooFewArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_chi_square(s);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dist_chi_square takes exactly 2 arguments", 3,
                            "20.14.2"));
}

TEST(DistributionArguments, DISABLED_ChiSquareWithTooManyArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_chi_square(s, 3, 1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dist_chi_square takes exactly 2 arguments", 3,
                            "20.14.2"));
}

TEST(DistributionArguments, DISABLED_ChiSquareWithNoArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_chi_square();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dist_chi_square takes exactly 2 arguments", 3,
                            "20.14.2"));
}

TEST(DistributionSeed, DISABLED_AChiSquareLiteralSeedIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_chi_square(5, 3);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the seed of $dist_chi_square shall be a variable it can write back", 3,
      "20.14.2"));
}

TEST(DistributionArguments, TWithItsArgumentsIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_t(s, 4);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(DistributionArguments, DISABLED_TWithTooFewArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_t(s);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dist_t takes exactly 2 arguments", 3, "20.14.2"));
}

TEST(DistributionArguments, DISABLED_TWithTooManyArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_t(s, 4, 1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dist_t takes exactly 2 arguments", 3, "20.14.2"));
}

TEST(DistributionArguments, DISABLED_TWithNoArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_t();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dist_t takes exactly 2 arguments", 3, "20.14.2"));
}

TEST(DistributionSeed, DISABLED_ATLiteralSeedIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_t(5, 4);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "the seed of $dist_t shall be a variable it can write back",
                    3, "20.14.2"));
}

TEST(DistributionArguments, ErlangWithItsArgumentsIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_erlang(s, 2, 7);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(DistributionArguments, DISABLED_ErlangWithTooFewArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_erlang(s, 2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dist_erlang takes exactly 3 arguments", 3,
                            "20.14.2"));
}

TEST(DistributionArguments, DISABLED_ErlangWithTooManyArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_erlang(s, 2, 7, 1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dist_erlang takes exactly 3 arguments", 3,
                            "20.14.2"));
}

TEST(DistributionArguments, DISABLED_ErlangWithNoArgumentsIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_erlang();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dist_erlang takes exactly 3 arguments", 3,
                            "20.14.2"));
}

TEST(DistributionSeed, DISABLED_AnErlangLiteralSeedIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer s, a, b, x;\n"
      "  initial x = $dist_erlang(5, 2, 7);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "the seed of $dist_erlang shall be a variable it can write back", 3,
      "20.14.2"));
}

}  // namespace
