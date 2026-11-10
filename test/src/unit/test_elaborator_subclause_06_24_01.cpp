#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <string_view>

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

TEST(CastOperatorElaboration,
     DISABLED_SizeCastToAParameterWidthOfZeroOrLessReported) {
  std::string src =
      "package p;\n"
      "  parameter int P = 17;\n"
      "  function automatic logic [7:0] pf(logic [7:0] x);\n"
      "    return (P - 18)'(x);\n"
      "  endfunction\n"
      "endpackage\n"
      "class C;\n"
      "  localparam int W = 0;\n"
      "  function logic [7:0] cf(logic [7:0] x); return W'(x); endfunction\n"
      "endclass\n"
      "module m #(parameter int Q = 16);\n"
      "  localparam int L = Q - 20;\n"
      "  logic [7:0] x, y, z, ok;\n"
      "  assign y = (Q - 16)'(x);\n"
      "  initial z = L'(x);\n"
      "  initial ok = (Q - 15)'(x);\n"
      "endmodule\n";
  ElabFixture f;
  ElaborateSrc(src, f);
  constexpr std::string_view kReport =
      "size cast target width must be a positive constant";
  for (std::string_view at :
       {"(P - 18)'(x)", "W'(x)", "(Q - 16)'(x)", "L'(x)"}) {
    SCOPED_TRACE(at);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kReport,
                              LineHolding(src, at), "6.24.1"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kReport,
                             LineHolding(src, "(Q - 15)'(x)"), "6.24.1"));
}

TEST(CastOperatorElaboration,
     DISABLED_AggregateWithAnElementOfNoPackedRepresentationReported) {
  std::string src =
      "typedef struct { real r; int i; } real_st;\n"
      "typedef struct { bit f; shortreal s; } shortreal_st;\n"
      "typedef struct { bit f; union { int i; shortreal f; } n; } union_st;\n"
      "typedef struct { chandle h; } chandle_st;\n"
      "typedef struct { event e; } event_st;\n"
      "typedef bit [127:0] b128;\n"
      "package p;\n"
      "  function automatic b128 pf(real_st v); return b128'(v); endfunction\n"
      "endpackage\n"
      "function automatic b128 uf(shortreal_st v);\n"
      "  return b128'(v);\n"
      "endfunction\n"
      "class C;\n"
      "  function b128 cf(union_st v); return b128'(v); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  chandle_st ch;\n"
      "  event_st ev;\n"
      "  realtime rt [2];\n"
      "  union_st u;\n"
      "  b128 a, b, c, d;\n"
      "  initial a = b128'(ch);\n"
      "  initial b = b128'(ev);\n"
      "  initial c = b128'(rt);\n"
      "  initial u = union_st'(d);\n"
      "endmodule\n";
  ElabFixture f;
  ElaborateSrc(src, f);
  for (std::string_view at :
       {"return b128'(v); endfunction\nendpackage", "  return b128'(v);\n",
        "cf(union_st v)", "b128'(ch)", "b128'(ev)", "b128'(rt)",
        "union_st'(d)"}) {
    SCOPED_TRACE(at);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "packed representation",
                              LineHolding(src, at), "6.24.1"));
  }
}

TEST(CastOperatorElaboration, AggregateOfPackableElementsCastAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "typedef struct { bit f; int i; logic [3:0] k; } pk_st;\n"
      "typedef struct { pk_st inner; byte b [2]; } nest_st;\n"
      "typedef bit [$bits(pk_st) - 1 : 0] pk_bits;\n"
      "typedef logic [$bits(nest_st) - 1 : 0] nest_bits;\n"
      "typedef bit [95:0] b96;\n"
      "package p;\n"
      "  function automatic pk_bits pf(pk_st v); return pk_bits'(v); "
      "endfunction\n"
      "endpackage\n"
      "class C;\n"
      "  function nest_st cf(nest_bits v); return nest_st'(v); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  nest_st n;\n"
      "  int ia [3];\n"
      "  nest_bits a;\n"
      "  b96 b;\n"
      "  initial a = nest_bits'(n);\n"
      "  initial b = b96'(ia);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
