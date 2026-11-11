#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(NetAliasingElaboration, AliasThreeNetsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b, c;\n"
      "  alias a = b = c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetAliasingElaboration, AliasBitSelectConcatElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire [31:0] A, B;\n"
      "  alias {A[7:0],A[15:8],A[23:16],A[31:24]} = B;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetAliasingElaboration, AliasStoresNetsInRtlir) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b;\n"
      "  alias a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  ASSERT_FALSE(design->top_modules[0]->aliases.empty());
  EXPECT_EQ(design->top_modules[0]->aliases[0].nets.size(), 2u);
}

TEST(NetAliasingElaboration, MultipleAliasStatementsAccumulate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b, c;\n"
      "  alias a = b;\n"
      "  alias b = c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_EQ(design->top_modules[0]->aliases.size(), 2u);
}

TEST(NetAliasingElaboration, AliasVariableIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  wire b;\n"
      "  alias a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "variables cannot appear in alias statements", 4,
                            "10.11"));
}

TEST(NetAliasingElaboration, AliasSelfIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire a;\n"
      "  alias a = a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "net 'a' aliased to itself",
                            3, "10.11"));
}

TEST(NetAliasingElaboration, AliasWandToWorIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wand a;\n"
      "  wor b;\n"
      "  alias a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'a' and 'b' are different net types", 4, "10.11"));
}

TEST(NetAliasingElaboration, AliasSameNetTypeOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wand a, b;\n"
      "  alias a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetAliasingElaboration, AliasDifferentWidthNetsIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire [7:0] a;\n"
      "  wire [3:0] b;\n"
      "  alias a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'a' has width 8 but 'b' has width 4", 4, "10.11"));
}

TEST(NetAliasingElaboration, AliasStructuredOperandWidthMismatchIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire [7:0] A, B;\n"
      "  alias {A[3:0]} = B;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "members of alias statement have different widths",
                            3, "10.11"));
}

TEST(NetAliasingElaboration, AliasHierarchicalRefIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module child;\n"
      "  wire x;\n"
      "endmodule\n"
      "module m;\n"
      "  child c1();\n"
      "  wire a;\n"
      "  alias a = c1.x;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical references cannot be used in alias statements", 7,
      "10.11"));
}

TEST(NetAliasingElaboration, AliasDuplicateSpecificationIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire a, b;\n"
      "  alias a = b;\n"
      "  alias a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "alias between 'a' and 'b' specified more than once", 4, "10.11"));
}

TEST(NetAliasingElaboration, AliasDuplicateReversedOrderIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire a, b;\n"
      "  alias a = b;\n"
      "  alias b = a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "alias between 'b' and 'a' specified more than once", 4, "10.11"));
}

TEST(NetAliasingElaboration, DuplicateAliasCheckIsScopedPerModule) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module a;\n"
      "  wire x, y;\n"
      "  alias x = y;\n"
      "endmodule\n"
      "module b;\n"
      "  wire x, y;\n"
      "  alias x = y;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules.size(), 2u);
}

TEST(NetAliasingElaboration, AliasUndeclaredIdentifierCreatesImplicitNet) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a;\n"
      "  alias a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetAliasingElaboration, AliasAmongOtherModuleItems) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b, y;\n"
      "  assign y = 1;\n"
      "  alias a = b;\n"
      "  initial begin end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_FALSE(design->top_modules[0]->aliases.empty());
  EXPECT_FALSE(design->top_modules[0]->assigns.empty());
}

TEST(NetAliasingElaboration, AliasDuplicateBitCorrespondenceIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire [15:0] bus16;\n"
      "  wire [11:0] high12, low12;\n"
      "  alias bus16 = {high12[11:8], low12};\n"
      "  alias bus16 = {high12, low12[3:0]};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "alias bit correspondence specified more than once",
                            5, "10.11"));
}

TEST(NetAliasingElaboration, AliasBitSelfAliasViaConcatenationIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire [15:0] bus16;\n"
      "  wire [11:0] high12, low12;\n"
      "  alias bus16 = {high12, bus16[3:0]} = {bus16[15:12], low12};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net bits aliased to themselves in alias statement",
                            4, "10.11"));
}

TEST(NetAliasingElaboration, AliasBitSelfAliasWithParameterBoundIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  parameter LO = 3;\n"
      "  parameter HI = 15;\n"
      "  wire [15:0] bus16;\n"
      "  wire [11:0] high12, low12;\n"
      "  alias bus16 = {high12, bus16[LO:0]} = {bus16[HI:12], low12};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net bits aliased to themselves in alias statement",
                            6, "10.11"));
}

TEST(NetAliasingElaboration, AliasBitSelfAliasWithLocalparamBoundIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  localparam LO = 3;\n"
      "  localparam HI = 15;\n"
      "  wire [15:0] bus16;\n"
      "  wire [11:0] high12, low12;\n"
      "  alias bus16 = {high12, bus16[LO:0]} = {bus16[HI:12], low12};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net bits aliased to themselves in alias statement",
                            6, "10.11"));
}

TEST(NetAliasingElaboration, OperandThatIsNoNetLvalueIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w, a, b; wire [3:0] x; int i;\n"
      "  alias w = a & b;\n"
      "  alias w = 1'b1;\n"
      "  alias w = x[i];\n"
      "  alias x[3:i] = x;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {3u, 4u, 5u, 6u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "alias operand is not a net_lvalue", line,
                              "10.11"));
  }
}

TEST(NetAliasingElaboration, OperandOfAnIllegalCompositeFormIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w, a, b; wire [3:0] x;\n"
      "  alias w = {a, b}[0];\n"
      "  alias x[1:0] = {a, 1'b1};\n"
      "  alias x[1:0] = '{1: a, 0: b};\n"
      "  alias x = int'(x);\n"
      "endmodule\n",
      f);
  for (uint32_t line : {3u, 4u, 5u, 6u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "alias operand is not a net_lvalue", line,
                              "10.11"));
  }
}

TEST(NetAliasingElaboration, TypedPatternOperandWithKeysIsError) {
  ElabFixture f;
  ElaborateSrc(
      "typedef struct packed { logic [1:0] hi, lo; } pair_t;\n"
      "module m;\n"
      "  wire [3:0] x; wire [1:0] a, b;\n"
      "  alias x = pair_t'{hi: a, lo: b};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "alias operand is not a net_lvalue", 4, "10.11"));
}

TEST(NetAliasingElaboration, EveryNetLvalueFormElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "typedef struct packed { logic [1:0] hi, lo; } pair_t;\n"
      "module m;\n"
      "  parameter P = 1;\n"
      "  wire [3:0] x, z, u; wire [1:0] a, b, c, d; wire [1:0][1:0] y;\n"
      "  alias x[2] = a[0];\n"
      "  alias x[0 +: 2] = b;\n"
      "  alias y[1][0] = a[1];\n"
      "  alias x = pair_t'{c, d};\n"
      "  alias z = '{c, d};\n"
      "  alias u[P:0] = d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetAliasingElaboration, HierarchicalSelectOperandIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module child;\n"
      "  wire [1:0] x;\n"
      "endmodule\n"
      "module m;\n"
      "  child c1();\n"
      "  wire a;\n"
      "  alias a = c1.x[0];\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "hierarchical references cannot be used in alias statements", 7,
      "10.11"));
}

TEST(NetAliasingElaboration, VariableNamedThroughSelectIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire [7:0] w; logic [7:0] v;\n"
      "  alias w = v[7:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'v' is a variable, not a net", 3, "10.11"));
}

TEST(NetAliasingElaboration, WandToWorSelectIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wand [1:0] a; wor [1:0] b;\n"
      "  alias a = b[1:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'a' and 'b' are different net types", 3, "10.11"));
}

TEST(NetAliasingElaboration, WandLogicToWorLogicIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wand logic [1:0] a; wor logic [1:0] b;\n"
      "  alias a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'a' and 'b' are different net types", 3, "10.11"));
}

TEST(NetAliasingElaboration, SelfAliasOfRangeNotStartingAtZeroIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire [8:1] a; wire [3:0] b;\n"
      "  alias a = {a[8:5], b};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "net bits aliased to themselves in alias statement",
                            3, "10.11"));
}

TEST(NetAliasingElaboration, RepeatOnAscendingRangeIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire [0:3] p; wire [1:0] q;\n"
      "  alias p[0:1] = q;\n"
      "  alias p[0:1] = q[1:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "alias bit correspondence specified more than once",
                            4, "10.11"));
}

TEST(NetAliasingElaboration, WholeNetAliasRepeatedAsSelectsIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire [3:0] a, b;\n"
      "  alias a = b;\n"
      "  alias a[3:0] = b[3:0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "alias bit correspondence specified more than once",
                            4, "10.11"));
}

TEST(NetAliasingElaboration, AliasInGenerateLoopElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire [1:0] w, v;\n"
      "  for (genvar i = 0; i < 2; i++) begin : g\n"
      "    wire a, b;\n"
      "    alias a = b;\n"
      "    alias w[i] = v[i];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetAliasingElaboration, PatternOperandBitAliasedToItselfIsError) {
  ElabFixture f;
  ElaborateSrc(
      "typedef struct packed { logic [3:0] hi, lo; } pair_t;\n"
      "module m;\n"
      "  wire [7:0] w, v; wire [3:0] a, b;\n"
      "  alias w = pair_t'{a, w[3:0]};\n"
      "  alias v = '{v[7:4], b};\n"
      "endmodule\n",
      f);
  for (uint32_t line : {4u, 5u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "net bits aliased to themselves", line, "10.11"));
  }
}

TEST(NetAliasingElaboration, PatternAliasRepeatedAsConcatenationIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire [7:0] p; wire [3:0] q, r;\n"
      "  alias p = '{q, r};\n"
      "  alias {q, r} = p;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "alias bit correspondence specified more than once",
                            4, "10.11"));
}

TEST(NetAliasingElaboration, TypedPatternOperandItemWidthMismatchIsError) {
  ElabFixture f;
  ElaborateSrc(
      "typedef struct packed { logic [3:0] hi, lo; } pair_t;\n"
      "module m;\n"
      "  wire [7:0] w; wire [4:0] c; wire [2:0] d;\n"
      "  alias w = pair_t'{c, d};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "LHS assignment pattern item has 5 bits but "
                            "member 'hi' of its type has 4 bits",
                            4, "10.9"));
}

TEST(NetAliasingElaboration,
     ImplicitAliasNetUnderDefaultNettypeNoneIsReported) {
  ElabFixture f;
  ElaborateWithPreprocessor(
      "`default_nettype none\n"
      "module t; wire a; alias a = b; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "implicit net 'b' forbidden by `default_nettype none", 2, "22.8"));
}

TEST(NetAliasingElaboration,
     DeclaredAliasNetUnderDefaultNettypeNoneIsAccepted) {
  ElabFixture f;
  ElaborateWithPreprocessor(
      "`default_nettype none\n"
      "module t; wire a, b; alias a = b; endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(NetAliasingElaboration, ImplicitAliasNetTakesTheDefaultNettype) {
  ElabFixture ok;
  ElaborateWithPreprocessor(
      "`default_nettype wand\n"
      "module t; wand a; alias a = b; endmodule\n",
      ok);
  EXPECT_FALSE(ok.diag.HasErrors());
  ElabFixture f;
  ElaborateWithPreprocessor(
      "`default_nettype wand\n"
      "module t; wor a; alias a = b; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'a' and 'b' are different net types", 2, "10.11"));
}

TEST(NetAliasingElaboration, ImplicitAliasNetIsAScalar) {
  ElabFixture f;
  ElaborateSrc("module t; wire [3:0] a; alias a = b; endmodule\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'a' has width 4 but 'b' has width 1", 1, "10.11"));
}

TEST(NetAliasingElaboration, AliasChecksReachAnInterface) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus; logic v; wire w; wand x; wor y; wire s;\n"
      "  alias v = w;\n"
      "  alias x = y;\n"
      "  alias s = s;\n"
      "endinterface\n"
      "module t; bus u(); endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'v' is a variable, not a net", 2, "10.11"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'x' and 'y' are different net types", 3, "10.11"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "net 's' aliased to itself",
                            4, "10.11"));
}

}  // namespace
