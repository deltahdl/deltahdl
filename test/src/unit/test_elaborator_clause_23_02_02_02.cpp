#include "fixture_elaborator.h"

namespace {

TEST(AnsiStylePortDeclarations, AnsiPortRedeclaredAsNetIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input logic [7:0] a, output logic y);\n"
      "  wire [7:0] a;\n"
      "  assign y = a[0];\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(AnsiStylePortDeclarations, AnsiPortRedeclaredAsVariableIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input logic [7:0] a, output logic y);\n"
      "  logic [7:0] a;\n"
      "  assign y = a[0];\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(AnsiStylePortDeclarations, DuplicateAnsiPortNameIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input logic a, output logic a);\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(AnsiStylePortDeclarations, DuplicateExplicitlyNamedAnsiPortIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(output .P1(a), output .P1(b));\n"
      "  logic a, b;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(AnsiStylePortDeclarations, AnsiPortsElaborateDirectionAndWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input logic [7:0] a, output logic [3:0] b);\n"
      "  assign b = a[3:0];\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(design->top_modules[0]->ports[0].width, 8u);
  EXPECT_EQ(design->top_modules[0]->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(design->top_modules[0]->ports[1].width, 4u);
}

// §23.2.2.2: the self-determined type of an explicitly named port's connection
// expression becomes the type of the port. A part-select `.P1(r[3:0])` makes
// P1 a 4-bit port and a concatenation `.P2({a, b})` a 16-bit port, independent
// of the declared widths of r, a, and b. This mirrors the LRM mymod example.
TEST(AnsiStylePortDeclarations, ExplicitPortExprSelfDeterminedTypeSetsWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(output .P1(r[3:0]), output .P2({a, b}));\n"
      "  logic [7:0] r;\n"
      "  logic [7:0] a, b;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& ports = design->top_modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[0].name, "P1");
  EXPECT_EQ(ports[0].width, 4u);
  EXPECT_EQ(ports[1].name, "P2");
  EXPECT_EQ(ports[1].width, 16u);
}

// §23.2.2.2: when the port expression is a simple identifier, the port adopts
// the self-determined width of the referenced object.
TEST(AnsiStylePortDeclarations, ExplicitPortExprSimpleIdentifierWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(output .P1(r));\n"
      "  logic [7:0] r;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& ports = design->top_modules[0]->ports;
  ASSERT_EQ(ports.size(), 1u);
  EXPECT_EQ(ports[0].name, "P1");
  EXPECT_EQ(ports[0].width, 8u);
}

// §23.2.2.2: a bit-select port expression is self-determined to one bit,
// independent of the width of the selected vector.
TEST(AnsiStylePortDeclarations, ExplicitPortExprBitSelectIsOneBit) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(output .P1(r[2]));\n"
      "  logic [7:0] r;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& ports = design->top_modules[0]->ports;
  ASSERT_EQ(ports.size(), 1u);
  EXPECT_EQ(ports[0].width, 1u);
}

// §23.2.2.2: an ascending indexed part-select (`base +: width`) is as wide as
// its constant width operand.
TEST(AnsiStylePortDeclarations, ExplicitPortExprIndexedPlusPartSelectWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(output .P1(r[2 +: 3]));\n"
      "  logic [7:0] r;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& ports = design->top_modules[0]->ports;
  ASSERT_EQ(ports.size(), 1u);
  EXPECT_EQ(ports[0].width, 3u);
}

// §23.2.2.2: a descending indexed part-select (`base -: width`) is likewise as
// wide as its constant width operand.
TEST(AnsiStylePortDeclarations, ExplicitPortExprIndexedMinusPartSelectWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(output .P1(r[5 -: 2]));\n"
      "  logic [7:0] r;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& ports = design->top_modules[0]->ports;
  ASSERT_EQ(ports.size(), 1u);
  EXPECT_EQ(ports[0].width, 2u);
}

// §23.2.2.2: the self-determined type includes signedness -- a simple signed
// reference makes the port signed, while a composite expression such as a
// concatenation is unsigned.
TEST(AnsiStylePortDeclarations, ExplicitPortExprSelfDeterminedSignedness) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(output .P1(rs), output .P2({a, b}));\n"
      "  logic signed [7:0] rs;\n"
      "  logic [7:0] a, b;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& ports = design->top_modules[0]->ports;
  ASSERT_EQ(ports.size(), 2u);
  EXPECT_EQ(ports[0].name, "P1");
  EXPECT_TRUE(ports[0].is_signed);
  EXPECT_EQ(ports[1].name, "P2");
  EXPECT_FALSE(ports[1].is_signed);
}

TEST(AnsiStylePortDeclarations, AnsiPortBodyDeclDifferentNameIsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input logic a, output logic y);\n"
      "  logic b;\n"
      "  assign y = a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
