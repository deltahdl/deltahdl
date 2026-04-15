#include "fixture_elaborator.h"

namespace {

TEST(NonAnsiStylePortDeclarations, BasicInputOutputElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(a, b);\n"
      "  input a;\n"
      "  output b;\n"
      "  assign b = a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->top_modules[0]->ports.size(), 2u);
}

TEST(NonAnsiStylePortDeclarations, ExplicitPortsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(.a(i), .b(i));\n"
      "  inout i;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NonAnsiStylePortDeclarations, TwoImplicitPortsSameNetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(a, a);\n"
      "  input a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NonAnsiStylePortDeclarations, MixedDirectionExplicitPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(.p({a, e}));\n"
      "  input a;\n"
      "  output e;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NonAnsiStylePortDeclarations, Example1SignednessElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(a, b, c, d, e, f, g, h);\n"
      "  input [7:0] a;\n"
      "  input [7:0] b;\n"
      "  input signed [7:0] c;\n"
      "  input signed [7:0] d;\n"
      "  output [7:0] e;\n"
      "  output [7:0] f;\n"
      "  output signed [7:0] g;\n"
      "  output signed [7:0] h;\n"
      "  wire signed [7:0] b;\n"
      "  wire [7:0] c;\n"
      "  logic signed [7:0] f;\n"
      "  logic [7:0] g;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NonAnsiStylePortDeclarations, DuplicateExplicitPortNameIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(.a(x), .a(y));\n"
      "  input x, y;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(NonAnsiStylePortDeclarations, PortWithoutDirectionInBodyIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(a, b);\n"
      "  input a;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(NonAnsiStylePortDeclarations, DuplicatePortDeclarationIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(a);\n"
      "  input a;\n"
      "  input a;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(NonAnsiStylePortDeclarations, CompletePortDeclRedeclaredAsNetIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(a);\n"
      "  input wire [7:0] a;\n"
      "  wire [7:0] a;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(f.has_errors);
}

TEST(NonAnsiStylePortDeclarations, PartialPortDeclMatchingRanges) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(a);\n"
      "  input [7:0] a;\n"
      "  wire [7:0] a;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NonAnsiStylePortDeclarations, PartialPortDeclMismatchedRangesIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(a);\n"
      "  input [7:0] a;\n"
      "  wire [3:0] a;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
