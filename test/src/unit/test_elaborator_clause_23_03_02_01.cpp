
#include "fixture_elaborator.h"

namespace {

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
      "  logic x, y, z;\n"
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
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a, input logic [7:0] b = 8'hFF);\n"
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
  ASSERT_GE(bindings.size(), 2u);
  EXPECT_EQ(bindings[0].port_name, "a");
  EXPECT_NE(bindings[0].connection, nullptr);
  EXPECT_EQ(bindings[1].port_name, "b");
  EXPECT_NE(bindings[1].connection, nullptr);
}

TEST(OrderedPortElaboration, BlankInputWithDefaultUsesDefault) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a, input logic [7:0] b = 8'hFF);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x;\n"
      "  child u(x, );\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_GE(bindings.size(), 2u);
  EXPECT_EQ(bindings[0].port_name, "a");
  EXPECT_NE(bindings[0].connection, nullptr);
  EXPECT_EQ(bindings[1].port_name, "b");
  EXPECT_NE(bindings[1].connection, nullptr);
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
  EXPECT_GT(f.diag.WarningCount() + f.diag.ErrorCount(), 0u);
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

TEST(OrderedPortElaboration, OrderedOutputPortNotToVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(output logic a, output logic b);\n"
      "  assign a = 1'b0;\n"
      "  assign b = 1'b1;\n"
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
  EXPECT_EQ(bindings[0].port_name, "a");
  EXPECT_EQ(bindings[0].direction, delta::Direction::kOutput);
  EXPECT_EQ(bindings[1].port_name, "b");
  EXPECT_EQ(bindings[1].direction, delta::Direction::kOutput);
}

}  // namespace
