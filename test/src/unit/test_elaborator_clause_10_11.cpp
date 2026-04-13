#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(NetAliasingElaboration, AliasTwoNetsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b;\n"
      "  alias a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

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

TEST(NetAliasingElaboration, AliasBothVariablesIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  alias a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(NetAliasingElaboration, AliasRegToNetIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  reg r;\n"
      "  wire w;\n"
      "  alias r = w;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(NetAliasingElaboration, AliasWandToWireIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wand a;\n"
      "  wire b;\n"
      "  alias a = b;\n"
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

TEST(NetAliasingElaboration, AliasSelfViaConcatenationIsError) {
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

}  // namespace
