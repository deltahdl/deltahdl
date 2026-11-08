#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

TEST(CastOperatorElaboration, CastInParameterElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = int'(3.14);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CastOperatorElaboration, CastInInitialElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  int b;\n"
      "  initial b = int'(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CastOperatorElaboration, SignedCastElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial b = signed'(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CastOperatorElaboration, VoidCastElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int f(); return 1; endfunction\n"
      "  initial void'(f());\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CastOperatorElaboration, CastInContinuousAssignElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [31:0] y;\n"
      "  assign y = int'(a);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CastOperatorSim, CastSigned) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  int result;\n"
      "  initial begin\n"
      "    x = 8'hFF;\n"
      "    result = signed'(x);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFFu);
}

TEST(CastOperatorSim, CastUnsigned) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  integer x;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    x = -1;\n"
      "    result = unsigned'(x);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFFu);
}

TEST(CastOperatorSim, CastShortint) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    x = 32'h1234ABCD;\n"
      "    result = shortint'(x);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.ToUint64(), 0xFFFFABCDu);
}

TEST(TypeOperatorSim, TypeOpStructMemberWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] field_a;\n"
      "    logic [7:0] field_b;\n"
      "  } my_struct;\n"
      "  my_struct s;\n"
      "  int result;\n"
      "  initial begin\n"
      "    s = 16'hCAFE;\n"
      "    result = s;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCAFEu);
}

TEST(CastOperatorSim, CastConcatToShortint) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  shortint result;\n"
      "  initial result = shortint'({8'hFA, 8'hCE});\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFACEu);
}

TEST(CastOperatorElaboration, SizeCastZeroWidthLiteralError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] r;\n"
      "  initial r = 0'(x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "size cast target width must be a positive constant", 4, "6.24.1"));
}

TEST(CastOperatorElaboration, SizeCastZeroWidthConstExprError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] r;\n"
      "  initial r = (2 - 2)'(x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "size cast target width must be a positive constant", 4, "6.24.1"));
}

TEST(CastOperatorElaboration, SizeCastPositiveWidthOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  logic [3:0] r;\n"
      "  initial r = 4'(x);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CastOperatorElaboration, RealVarInSignedCastError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real rv;\n"
      "  int r;\n"
      "  initial r = signed'(rv);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a signing cast works only on an integral value", 4,
                            "6.24.1"));
}

TEST(CastOperatorElaboration, RealVarInUnsignedCastError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real rv;\n"
      "  int r;\n"
      "  initial r = unsigned'(rv);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a signing cast works only on an integral value", 4,
                            "6.24.1"));
}

TEST(CastOperatorElaboration, RealLiteralInSignedCastError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int r;\n"
      "  initial r = signed'(2.5);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a signing cast works only on an integral value", 3,
                            "6.24.1"));
}

TEST(CastOperatorElaboration, RealVarInSizeCastError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real rv;\n"
      "  logic [7:0] r;\n"
      "  initial r = 8'(rv);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a size cast works only on an integral value", 4,
                            "6.24.1"));
}

TEST(CastOperatorElaboration, RealLiteralInSizeCastError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] r;\n"
      "  initial r = 8'(2.5);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a size cast works only on an integral value", 3,
                            "6.24.1"));
}

TEST(CastOperatorElaboration, ShortrealVarInSignedCastError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  shortreal s;\n"
      "  int r;\n"
      "  initial r = signed'(s);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a signing cast works only on an integral value", 4,
                            "6.24.1"));
}

TEST(CastOperatorElaboration, TimeLiteralInSignedCastError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  int r;\n"
      "  initial r = signed'(2.1ns);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a signing cast works only on an integral value", 4,
                            "6.24.1"));
}

TEST(CastOperatorElaboration, TimeLiteralInSizeCastError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  logic [7:0] r;\n"
      "  initial r = 8'(2.1ns);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a size cast works only on an integral value", 4,
                            "6.24.1"));
}

TEST(CastOperatorSim, CastByteTruncate) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = byte'(32'hABCD);\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

TEST(CastOperatorElaboration, SizeCastZeroWidthNames6_24_1) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  logic [7:0] r;\n"
      "  initial r = 0'(x);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "size cast target width must be a positive constant", 4, "6.24.1"));
}

TEST(CastOperatorElaboration, SizeCastInLocalparamSizesAPackedRange) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int W = 4'(20);\n"
      "  logic [W-1:0] r;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* var = FindVar(design, "m", "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->width, 4u);
}

TEST(CastOperatorElaboration, RealLiteralInSignedCastInForkArmError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int r;\n"
      "  initial fork\n"
      "    r = signed'(2.5);\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a signing cast works only on an integral value", 4,
                            "6.24.1"));
}

TEST(CastOperatorElaboration, RealLiteralInSignedCastInForInitializerError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int r;\n"
      "  int i;\n"
      "  initial\n"
      "    for (r = signed'(2.5); i < 1; i = i + 1)\n"
      "      i = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a signing cast works only on an integral value", 5,
                            "6.24.1"));
}

TEST(CastOperatorElaboration, RealLiteralInSignedCastInForStepError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int r;\n"
      "  int i;\n"
      "  initial\n"
      "    for (i = 0; i < 1; r = signed'(2.5))\n"
      "      i = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a signing cast works only on an integral value", 5,
                            "6.24.1"));
}

TEST(CastOperatorElaboration,
     RealLiteralInSignedCastInAssertionPassStatementError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int r;\n"
      "  logic ok;\n"
      "  initial assert (ok) r = signed'(2.5);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a signing cast works only on an integral value", 4,
                            "6.24.1"));
}

TEST(CastOperatorElaboration,
     RealLiteralInSignedCastInAssertionFailStatementError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int r;\n"
      "  logic armed;\n"
      "  initial assert (armed) else r = signed'(2.5);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a signing cast works only on an integral value", 4,
                            "6.24.1"));
}

TEST(CastOperatorElaboration, RealLiteralInSignedCastInRandcaseItemError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int r;\n"
      "  initial randcase 1: r = signed'(2.5); endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a signing cast works only on an integral value", 3,
                            "6.24.1"));
}

TEST(CastOperatorElaboration,
     RealLiteralInSignedCastInRandsequenceCodeBlockError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int r;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { r = signed'(2.5); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a signing cast works only on an integral value", 5,
                            "6.24.1"));
}

TEST(CastOperatorElaboration, NonIntegralOperandOfAnyFormRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  real r = 1.5;\n"
      "  string s = \"a\";\n"
      "  int arr[2];\n"
      "  chandle ch;\n"
      "  event ev;\n"
      "  struct {int a;} st;\n"
      "  class C;\n"
      "  endclass\n"
      "  C h;\n"
      "  int n;\n"
      "  logic [15:0] v;\n"
      "  initial begin\n"
      "    v = 8'(r * 2.0);\n"
      "    v = 8'(n + r);\n"
      "    v = 8'(-r);\n"
      "    v = 8'(n ? r : 1);\n"
      "    v = 8'(n ? 2 : r);\n"
      "    v = 8'(2ns);\n"
      "    v = 8'(s);\n"
      "    v = 16'(h);\n"
      "    v = 8'(ch);\n"
      "    v = 8'(ev);\n"
      "    v = signed'(arr);\n"
      "    v = signed'(st);\n"
      "    v = 8'(r > 1.0);\n"
      "    v = 8'(-n);\n"
      "    v = 8'(n + 1);\n"
      "    v = 8'(v[3:0]);\n"
      "    v = signed'(v);\n"
      "    v = 8'(n ? 1 : 2);\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {14U, 15U, 16U, 17U, 18U, 19U, 20U, 21U, 22U, 23U}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "a size cast works only on an integral value",
                              line, "6.24.1"));
  }
  for (uint32_t line : {24U, 25U}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "a signing cast works only on an integral value",
                              line, "6.24.1"));
  }
  for (uint32_t line : {26U, 27U, 28U, 29U, 30U, 31U}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                               "works only on an integral value", line,
                               "6.24.1"));
  }
}

}  // namespace
