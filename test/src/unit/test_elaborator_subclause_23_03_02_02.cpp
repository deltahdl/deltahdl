#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(NamedPortConnectionElaboration, PortBindingDirection) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  child u0(.a(x), .b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1);
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_EQ(bindings.size(), 2);

  struct {
    const char* port_name;
    Direction direction;
  } const kExpected[] = {
      {"a", Direction::kInput},
      {"b", Direction::kOutput},
  };
  for (size_t i = 0; i < 2; ++i) {
    EXPECT_EQ(bindings[i].port_name, kExpected[i].port_name);
    EXPECT_EQ(bindings[i].direction, kExpected[i].direction);
  }
}

TEST(NamedPortConnectionElaboration, PortBindingPortMismatch) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic x;\n"
      "  child u0(.bogus(x));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1);

  ASSERT_EQ(mod->children[0].port_bindings.size(), 1);
  EXPECT_EQ(mod->children[0].port_bindings[0].port_name, "a");
  EXPECT_GT(f.diag.ErrorCount(), 0u);
}

TEST(NamedPortConnectionElaboration, EmptyNamedPortDoesNotUseDefault) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a = 8'hFF, output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] y;\n"
      "  child u(.a(), .b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  const auto& bindings = mod->children[0].port_bindings;
  const RtlirPortBinding* a_binding = nullptr;
  for (const auto& b : bindings) {
    if (b.port_name == "a") {
      a_binding = &b;
      break;
    }
  }
  ASSERT_NE(a_binding, nullptr);
  ASSERT_NE(mod->children[0].resolved, nullptr);
  const RtlirPort* a_port = nullptr;
  for (const auto& p : mod->children[0].resolved->ports) {
    if (p.name == "a") {
      a_port = &p;
      break;
    }
  }
  ASSERT_NE(a_port, nullptr);
  EXPECT_NE(a_port->default_value, nullptr);
  ASSERT_NE(a_binding->connection, nullptr);
  EXPECT_EQ(a_binding->connection->kind, ExprKind::kUnbasedUnsizedLiteral);
  EXPECT_EQ(a_binding->connection->text, "'z");
}

TEST(NamedPortConnectionElaboration, OmittedPortWithoutDefaultIsUnconnected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, input logic b, output logic c);\n"
      "  assign c = a ^ b;\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  child u(.a(x), .c(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  const auto& bindings = mod->children[0].port_bindings;
  for (const auto& b : bindings) {
    if (b.port_name != "b") continue;
    ASSERT_NE(b.connection, nullptr);
    EXPECT_EQ(b.connection->kind, ExprKind::kUnbasedUnsizedLiteral);
  }
}

TEST(NamedPortConnectionElaboration, OmittedOutputPortHasNoBinding) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, output logic b, output logic c);\n"
      "  assign b = a;\n"
      "  assign c = ~a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  child u(.a(x), .b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  const auto& bindings = mod->children[0].port_bindings;
  for (const auto& b : bindings) {
    EXPECT_NE(b.port_name, "c");
  }
}

TEST(NamedPortConnectionElaboration, OmittedPortWithDefaultUsesDefault) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic [7:0] a,\n"
      "             input logic [7:0] rst_n = 8'h01,\n"
      "             output logic [7:0] b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] x, y;\n"
      "  child u(.a(x), .b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  const auto& bindings = mod->children[0].port_bindings;
  const RtlirPortBinding* rst_binding = nullptr;
  for (const auto& bnd : bindings) {
    if (bnd.port_name == "rst_n") {
      rst_binding = &bnd;
      break;
    }
  }
  ASSERT_NE(rst_binding, nullptr);
  ASSERT_NE(mod->children[0].resolved, nullptr);
  const RtlirPort* rst_port = nullptr;
  for (const auto& p : mod->children[0].resolved->ports) {
    if (p.name == "rst_n") {
      rst_port = &p;
      break;
    }
  }
  ASSERT_NE(rst_port, nullptr);
  EXPECT_NE(rst_port->default_value, nullptr);
  EXPECT_EQ(rst_binding->connection, rst_port->default_value);
}

TEST(NamedPortConnectionElaboration, ReversedOrderBindsCorrectly) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic x, y;\n"
      "  child u(.b(y), .a(x));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_EQ(bindings.size(), 2u);
  bool found_a = false, found_b = false;
  for (const auto& b : bindings) {
    if (b.port_name == "a") {
      EXPECT_EQ(b.direction, Direction::kInput);
      found_a = true;
    } else if (b.port_name == "b") {
      EXPECT_EQ(b.direction, Direction::kOutput);
      found_b = true;
    }
  }
  EXPECT_TRUE(found_a);
  EXPECT_TRUE(found_b);
}

TEST(NamedPortConnectionElaboration, PortNameNamesNoPortNames23_3_2_2) {
  ElabFixture f;
  ElaborateSrc(
      "module child(input a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic x;\n"
      "  child c1(.nope(x));\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "not found on module", 5,
                            "23.3.2.2"));
}

TEST(NamedPortConnectionElaboration, PortConnectedTwiceIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module A(input i, output o, inout e);\n"
      "  assign o = i;\n"
      "endmodule\n"
      "module test;\n"
      "  wire a, b, c, d, e, f;\n"
      "  A ia(.i(a), .i(b), .o(c), .o(d), .e(e), .e(f), .i(a));\n"
      "endmodule\n",
      f, "test");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "port 'i' of module 'A'", 6,
                            "23.3.2.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "port 'o' of module 'A'", 6,
                            "23.3.2.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "port 'e' of module 'A'", 6,
                            "23.3.2.2"));
  size_t repeats = 0;
  for (const auto& d : f.diag.Diagnostics()) {
    if (d.message.find("connected more than once") != std::string::npos) {
      ++repeats;
    }
  }
  EXPECT_EQ(repeats, 3u);
}

TEST(NamedPortConnectionElaboration, EachPortConnectedOnceIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module A(input i, output o, inout e);\n"
      "  assign o = i;\n"
      "endmodule\n"
      "module test;\n"
      "  wire a, c, e;\n"
      "  A ia(.e(e), .o(c), .i(a));\n"
      "endmodule\n",
      f, "test");
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
