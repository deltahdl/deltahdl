#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace {

void ExpectSecondInputUsesDeclaredDefault(const char* instantiation) {
  ElabFixture f;
  std::string src =
      "module child(input logic [7:0] a, input logic [7:0] b = 8'hFF);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x;\n";
  src += instantiation;
  src += "endmodule\n";
  auto* design = ElaborateSrc(src, f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_GE(bindings.size(), 2u);
  EXPECT_EQ(bindings[0].port_name, "a");
  EXPECT_NE(bindings[0].connection, nullptr);
  EXPECT_EQ(bindings[1].port_name, "b");
  ASSERT_NE(mod->children[0].resolved, nullptr);
  ASSERT_GE(mod->children[0].resolved->ports.size(), 2u);
  EXPECT_EQ(bindings[1].connection,
            mod->children[0].resolved->ports[1].default_value);
  EXPECT_NE(bindings[1].connection, nullptr);
}

TEST(OrderedPortElaboration, SingleOrderedPortBindsByPosition) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  child u(x, y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_EQ(bindings.size(), 2u);
  EXPECT_EQ(bindings[0].port_name, "a");
  EXPECT_EQ(bindings[1].port_name, "b");
}

TEST(OrderedPortElaboration, OrderedPortDirectionMatchesChildPort) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, output logic b, inout logic c);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  wire z;\n"
      "  child u(x, y, z);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_EQ(bindings.size(), 3u);
  EXPECT_EQ(bindings[0].direction, delta::Direction::kInput);
  EXPECT_EQ(bindings[1].direction, delta::Direction::kOutput);
  EXPECT_EQ(bindings[2].direction, delta::Direction::kInout);
}

TEST(OrderedPortElaboration, OrderedPortWidthMatchesChildPort) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a, output logic [3:0] b);\n"
      "  assign b = a[3:0];\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x;\n"
      "  logic [3:0] y;\n"
      "  child u(x, y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_EQ(bindings.size(), 2u);
  EXPECT_EQ(bindings[0].width, 8u);
  EXPECT_EQ(bindings[1].width, 4u);
}

TEST(OrderedPortElaboration, BlankOrderedPortLeavesPortUnconnected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, output logic b, input logic c);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  child u(x, , y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_GE(bindings.size(), 3u);
  EXPECT_EQ(bindings[0].port_name, "a");
  EXPECT_NE(bindings[0].connection, nullptr);
  EXPECT_EQ(bindings[1].port_name, "b");
  EXPECT_EQ(bindings[1].connection, nullptr);
  EXPECT_EQ(bindings[2].port_name, "c");
  EXPECT_NE(bindings[2].connection, nullptr);
}

TEST(OrderedPortElaboration, TrailingOmittedInputUsesDefault) {
  ExpectSecondInputUsesDeclaredDefault("  child u(x);\n");
}

TEST(OrderedPortElaboration, BlankInputWithDefaultUsesDefault) {
  ExpectSecondInputUsesDeclaredDefault("  child u(x, );\n");
}

TEST(OrderedPortElaboration, BlankInputWithoutDefaultLeftUnconnected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a, input logic [7:0] b);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x;\n"
      "  child u(x, );\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_GE(bindings.size(), 2u);
  EXPECT_EQ(bindings[1].port_name, "b");
  ASSERT_NE(mod->children[0].resolved, nullptr);
  ASSERT_GE(mod->children[0].resolved->ports.size(), 2u);
  EXPECT_EQ(mod->children[0].resolved->ports[1].default_value, nullptr);
  ASSERT_NE(bindings[1].connection, nullptr);
  EXPECT_EQ(bindings[1].connection->kind,
            delta::ExprKind::kUnbasedUnsizedLiteral);
}

TEST(OrderedPortElaboration,
     TrailingOmittedInputWithoutDefaultLeftUnconnected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a, input logic [7:0] b);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x;\n"
      "  child u(x);\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  const auto& bindings = mod->children[0].port_bindings;
  bool a_connected = false;
  bool b_high_z = false;
  for (const auto& binding : bindings) {
    if (binding.port_name == "a" && binding.connection != nullptr)
      a_connected = true;
    if (binding.port_name == "b" && binding.connection != nullptr)
      b_high_z =
          binding.connection->kind == delta::ExprKind::kUnbasedUnsizedLiteral;
  }
  EXPECT_TRUE(a_connected);
  EXPECT_TRUE(b_high_z);
}

TEST(OrderedPortElaboration, ExcessOrderedPortsWarns) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  child u(x, y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_GT(f.diag.WarningCount() + (f.diag.HasErrors() ? 1u : 0u), 0u);
}

TEST(OrderedPortElaboration, OrderedPortConnectionExpressionPreserved) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, input logic b);\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  child u(x, y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_EQ(bindings.size(), 2u);
  ASSERT_NE(bindings[0].connection, nullptr);
  ASSERT_NE(bindings[1].connection, nullptr);
  EXPECT_EQ(bindings[0].connection->text, "x");
  EXPECT_EQ(bindings[1].connection->text, "y");
}

TEST(OrderedPortElaboration, AllPortsOrderedOnPortlessModuleElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child; endmodule\n"
      "module top;\n"
      "  child u();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  EXPECT_TRUE(mod->children[0].port_bindings.empty());
}

TEST(OrderedPortElaboration, NonAnsiChildPortsBindByPosition) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(a, b);\n"
      "  input [7:0] a;\n"
      "  output [7:0] b;\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x;\n"
      "  wire [7:0] y;\n"
      "  child u(x, y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_EQ(bindings.size(), 2u);
  EXPECT_EQ(bindings[0].port_name, "a");
  EXPECT_EQ(bindings[0].direction, delta::Direction::kInput);
  EXPECT_EQ(bindings[0].width, 8u);
  EXPECT_EQ(bindings[1].port_name, "b");
  EXPECT_EQ(bindings[1].direction, delta::Direction::kOutput);
  EXPECT_EQ(bindings[1].width, 8u);
}

TEST(OrderedPortElaboration, TooManyOrderedConnectionsNames23_3_2_1) {
  ElabFixture f;
  ElaborateSrc(
      "module child(input a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  child c1(x, y);\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), "too many ordered port", 5,
                              "23.3.2.1"));
}

}  // namespace
