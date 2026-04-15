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

TEST(AnsiStylePortDeclarations, ExplicitlyNamedAnsiPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(output .P1(r[3:0]), input R);\n"
      "  logic [7:0] r;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->ports[0].name, "P1");
}

TEST(AnsiStylePortDeclarations, GenericInterfaceAnsiPortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module cpuMod(interface d, interface j);\n"
      "endmodule\n",
      f, "cpuMod");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->ports.size(), 2u);
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
