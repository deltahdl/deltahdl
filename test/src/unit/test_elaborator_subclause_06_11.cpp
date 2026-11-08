#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(IntegerDataTypes, FixedWidthIntegerTypesTakeTabulatedWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte a;\n"
      "  shortint b;\n"
      "  int c;\n"
      "  longint d;\n"
      "  integer e;\n"
      "  time g;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 6u);
  EXPECT_EQ(mod->variables[0].width, 8u) << "byte";
  EXPECT_EQ(mod->variables[1].width, 16u) << "shortint";
  EXPECT_EQ(mod->variables[2].width, 32u) << "int";
  EXPECT_EQ(mod->variables[3].width, 64u) << "longint";
  EXPECT_EQ(mod->variables[4].width, 32u) << "integer";
  EXPECT_EQ(mod->variables[5].width, 64u) << "time";
}

TEST(IntegerDataTypes, UserDefinedWidthTypesDefaultToOneBit) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit a;\n"
      "  logic b;\n"
      "  reg c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 3u);
  EXPECT_EQ(mod->variables[0].width, 1u) << "bit";
  EXPECT_EQ(mod->variables[1].width, 1u) << "logic";
  EXPECT_EQ(mod->variables[2].width, 1u) << "reg";
}

TEST(IntegerDataTypes, UserDefinedWidthTypesTakeDeclaredVectorSize) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [7:0] a;\n"
      "  logic [15:0] b;\n"
      "  reg [31:0] c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 3u);
  EXPECT_EQ(mod->variables[0].width, 8u) << "bit [7:0]";
  EXPECT_EQ(mod->variables[1].width, 16u) << "logic [15:0]";
  EXPECT_EQ(mod->variables[2].width, 32u) << "reg [31:0]";
}

TEST(IntegerDataTypes, UserDefinedWidthFromParameterVectorSize) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter P = 16;\n"
      "  bit   [P-1:0] a;\n"
      "  logic [P-1:0] b;\n"
      "  reg   [P-1:0] c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 3u);
  EXPECT_EQ(mod->variables[0].width, 16u) << "bit [P-1:0]";
  EXPECT_EQ(mod->variables[1].width, 16u) << "logic [P-1:0]";
  EXPECT_EQ(mod->variables[2].width, 16u) << "reg [P-1:0]";
}

TEST(IntegerDataTypes, UserDefinedWidthFromLocalparamVectorSize) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam Q = 24;\n"
      "  bit   [Q-1:0] a;\n"
      "  logic [Q-1:0] b;\n"
      "  reg   [Q-1:0] c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 3u);
  EXPECT_EQ(mod->variables[0].width, 24u) << "bit [Q-1:0]";
  EXPECT_EQ(mod->variables[1].width, 24u) << "logic [Q-1:0]";
  EXPECT_EQ(mod->variables[2].width, 24u) << "reg [Q-1:0]";
}

}  // namespace
