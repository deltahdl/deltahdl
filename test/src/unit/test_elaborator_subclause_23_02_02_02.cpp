#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_type.h"

namespace {

TEST(AnsiStylePortDeclarations, AnsiPortRedeclaredAsNetIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input logic [7:0] a, output logic y);\n"
      "  wire [7:0] a;\n"
      "  assign y = a[0];\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "redeclaration of ANSI port 'a'", 2, "23.2.2.1"));
}

TEST(AnsiStylePortDeclarations, AnsiPortRedeclaredAsVariableIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input logic [7:0] a, output logic y);\n"
      "  logic [7:0] a;\n"
      "  assign y = a[0];\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "redeclaration of ANSI port 'a'", 2, "23.2.2.1"));
}

TEST(AnsiStylePortDeclarations, DuplicateAnsiPortNameIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input logic a, output logic a);\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "duplicate port name 'a'", 1,
                            "23.2.2.2"));
}

TEST(AnsiStylePortDeclarations, DuplicateExplicitlyNamedAnsiPortIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m(output .P1(a), output .P1(b));\n"
      "  logic a, b;\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "duplicate port name 'P1'", 1,
                            "23.2.2.2"));
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
