#include "fixture_elaborator.h"

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
  EXPECT_TRUE(f.has_errors);
}

TEST(NetAliasingElaboration, AliasSelfIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire a;\n"
      "  alias a = a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
}

// §10.11: the scope of an alias is limited to its module, so the
// "specified more than once" check must be confined to a single module. Two
// independent modules may each declare the same alias; the per-module reset of
// the duplicate-tracking set keeps the second from being mis-flagged as a
// repeat of the first.
TEST(NetAliasingElaboration, DuplicateAliasCheckIsScopedPerModule) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module a;\n"
      "  wire x, y;\n"
      "  alias x = y;\n"
      "endmodule\n"
      "module b;\n"
      "  wire x, y;\n"
      "  alias x = y;\n"
      "endmodule\n",
      f);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
