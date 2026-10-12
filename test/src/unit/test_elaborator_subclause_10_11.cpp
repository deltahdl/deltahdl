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

// §10.11: each member shall be the same size. Here a concatenation member is
// 4 bits wide while the whole-net member is 8 bits; the size rule must reject
// it even though the operand is structured (a select/concat), not a plain net.
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

// Restating an existing alias with its operands swapped is still the same
// alias and must be rejected. This exercises the operand-order normalization
// in the duplicate check, which a same-order repeat would not reach.
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

// §10.11: the scope of an alias is limited to its module, so the
// "specified more than once" check must be confined to a single module. Two
// independent modules may each declare the same alias; the per-module reset of
// the duplicate-tracking set keeps the second from being mis-flagged as a
// repeat of the first.
// Both modules have to be elaborated for the claim to be tested at all, and
// neither instantiates the other, so the two are roots of their own. That needs
// the auto-top form: given no top name, ElaborateSrc elaborates the last module
// alone, which would leave module a's alias never registered and the check
// never given the chance to carry over.
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
      f, "", /*auto_top=*/true);
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

// §10.11 Example A: two statements that share the top 4 and bottom 4 bits
// specify the same alias correspondence more than once, which is illegal. This
// drives the module-lifetime bit-correspondence set across concatenations.
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

// §10.11 Example B: a single statement whose operands place the same bits of
// bus16 at the same position aliases those bits to themselves, which is
// illegal even though no whole-net operand repeats.
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

// §10.11 Example B with parameter-based select bounds. §11.2.1 lets a
// constant_select bound be a parameter, which takes a different evaluation path
// than a literal; the bit-level self-alias check must still fire once the
// parameters resolve. LO/HI reproduce the bus16[3:0]/bus16[15:12] overlap.
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

// Same overlap driven by localparam bounds, the other §11.2.1 constant form
// that resolves through the module's parameter scope.
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

// §10.11 Syntax 10-6: an alias operand is a net_lvalue, so an operator
// expression, a literal and a select whose index or bound is no constant are
// each reported rather than dropped.
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

// §10.11 Syntax 10-6: a select is taken from a net, a concatenation holds
// net_lvalues alone, a pattern is positional, and a cast is no net_lvalue
// unless it types a pattern.
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

// §10.11 Syntax 10-6: a typed pattern is a net_lvalue only when its own items
// are written positionally.
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

// §10.11 Syntax 10-6: each form a net_lvalue takes elaborates -- a bit-select,
// an indexed part-select, a select of a select, a positional pattern with and
// without a type, and a select whose bound is a parameter.
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

// A hierarchical name with a constant select is a net_lvalue by its form, and
// §10.11 still bars it as a hierarchical reference.
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

// §10.11: a variable is barred from an alias statement even when the operand
// names it through a select.
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

// §10.11: nets of different net types may not be aliased, and a select counts
// as the net it is taken from.
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

// §10.11: the net type is the keyword the declaration wrote, so wand logic and
// wor logic differ although both carry the data type logic.
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

// §10.11: a net's bits aliased to themselves are found whatever index its range
// starts at. a[8:5] is the top four bits of `wire [8:1] a`, which the whole
// name places at the same positions.
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

// §10.11: an ascending range is read with its first index as the most
// significant bit, so p[0:1] written twice against q is one alias repeated.
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

// §10.11: an alias written once with whole nets and again with selects of the
// same bits is specified more than once.
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

// §10.11: each iteration of a loop generate block declares nets of its own, so
// the alias each iteration writes joins different nets and none repeats.
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

// §10.11 with Syntax 10-6: a positional pattern operand stands for its items'
// bits in order, as a concatenation does, typed or not, so a bit it places
// against itself is aliased to itself.
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

// §10.11: an alias a pattern operand specifies is the one a concatenation of
// the same nets specifies, so writing it both ways specifies it twice.
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

// §10.9 with Syntax 10-6: a typed pattern operand of an alias is the
// left-hand-side form of a net_lvalue, so each item has the bit count of the
// member it stands for, though the items' total matches the other operand.
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

}  // namespace
