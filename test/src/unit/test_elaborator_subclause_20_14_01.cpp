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

TEST(RandomSeedType, AShortintSeedIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  shortint seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RandomSeedType, ALongintSeedIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  longint seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RandomSeedType, ALogicVectorSeedIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [47:0] seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RandomSeedType, AnEnumVariableSeedIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  enum int {A, B} seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RandomSeedType, APackedStructVariableSeedIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  struct packed { bit [15:0] hi, lo; } seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RandomSeedType, DISABLED_ARealSeedInAModuleFunctionIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  function int f();\n"
      "    real seed;\n"
      "    return $random(seed);\n"
      "  endfunction\n"
      "  integer x;\n"
      "  initial x = f();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$random cannot take its seed from a variable that is not integral", 4,
      "20.14.1"));
}

TEST(RandomSeedType, ARealSeedInAProgramIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "program p;\n"
      "  real seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endprogram\n"
      "module m;\n"
      "  p u();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$random cannot take its seed from a variable that is not integral", 4,
      "20.14.1"));
}

TEST(RandomSeedType, DISABLED_ARealSeedInAContinuousAssignmentIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  real seed;\n"
      "  wire [31:0] w;\n"
      "  assign w = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$random cannot take its seed from a variable that is not integral", 4,
      "20.14.1"));
}

TEST(RandomSeedType, ARealSeedInANetDeclarationAssignmentIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  real seed;\n"
      "  wire [31:0] w = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$random cannot take its seed from a variable that is not integral", 3,
      "20.14.1"));
}

TEST(RandomSeedType, DISABLED_ARealSeedInAClassMethodIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  class C;\n"
      "    real seed;\n"
      "    function int f();\n"
      "      return $random(seed);\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$random cannot take its seed from a variable that is not integral", 5,
      "20.14.1"));
}

TEST(RandomSeedType,
     DISABLED_ARealSeedInAPackageVariableInitializerIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "package pk;\n"
      "  real seed;\n"
      "  int x = $random(seed);\n"
      "endpackage\n"
      "module m;\n"
      "  import pk::*;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$random cannot take its seed from a variable that is not integral", 3,
      "20.14.1"));
}

TEST(RandomSeedType, DISABLED_ARealSeedInAPackageFunctionIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "package pk;\n"
      "  function int f();\n"
      "    real seed;\n"
      "    return $random(seed);\n"
      "  endfunction\n"
      "endpackage\n"
      "module m;\n"
      "  import pk::*;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$random cannot take its seed from a variable that is not integral", 4,
      "20.14.1"));
}

TEST(RandomSeedType, DISABLED_ALiteralSeedIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer x;\n"
      "  initial x = $random(5);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$random takes its seed from a variable", 3,
                            "20.14.1"));
}

TEST(RandomSeedType, DISABLED_AnExpressionSeedIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer a;\n"
      "  integer x;\n"
      "  initial x = $random(a + 1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$random takes its seed from a variable", 4,
                            "20.14.1"));
}

TEST(RandomSeedType, DISABLED_AParameterSeedIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  parameter int P = 3;\n"
      "  integer x;\n"
      "  initial x = $random(P);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$random takes its seed from a variable", 4,
                            "20.14.1"));
}

TEST(RandomSeedType, DISABLED_ANetSeedIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  wire [31:0] n;\n"
      "  integer x;\n"
      "  initial x = $random(n);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$random takes its seed from a variable", 4,
                            "20.14.1"));
}

TEST(RandomSeedType, DISABLED_AChandleSeedIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  chandle seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$random cannot take its seed from a variable that is not integral", 4,
      "20.14.1"));
}

TEST(RandomSeedType, DISABLED_AClassHandleSeedIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  class C;\n"
      "  endclass\n"
      "  C seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$random cannot take its seed from a variable that is not integral", 6,
      "20.14.1"));
}

TEST(RandomSeedType, DISABLED_AnUnpackedArraySeedIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  int seed [2];\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$random cannot take its seed from a variable that is not integral", 4,
      "20.14.1"));
}

TEST(RandomSeedType, DISABLED_AnEventSeedIsReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  event seed;\n"
      "  integer x;\n"
      "  initial x = $random(seed);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$random cannot take its seed from a variable that is not integral", 4,
      "20.14.1"));
}

TEST(RandomArguments, DISABLED_EmptyParenthesesAreReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer x;\n"
      "  initial x = $random();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$random takes no argument list or exactly one seed argument", 3,
      "20.14.1"));
}

TEST(RandomArguments, NoArgumentListIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  integer x;\n"
      "  initial x = $random;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

TEST(RandomArguments, DISABLED_TwoArgumentsAreReported) {
  ElabFixture f;
  ElaborateSrcAllowingParseErrors(
      "module m;\n"
      "  integer a, b, x;\n"
      "  initial x = $random(a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "$random takes no argument list or exactly one seed argument", 3,
      "20.14.1"));
}

TEST(RandomArguments, OneSeedArgumentIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  integer a, x;\n"
      "  initial x = $random(a);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
