#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(NamedPortConnectionElaboration, PortBindingResolvesChild) {
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
  EXPECT_NE(mod->children[0].resolved, nullptr);
  EXPECT_EQ(mod->children[0].resolved->name, "child");
  EXPECT_EQ(mod->children[0].port_bindings.size(), 2);
}

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

  EXPECT_EQ(mod->children[0].port_bindings.size(), 1);
  EXPECT_GT(f.diag.WarningCount(), 0u);
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
  // The rule only bites when the port actually carries a default: confirm the
  // declared default survived elaboration, then confirm it was deliberately
  // NOT substituted for the explicit empty named connection. Without the first
  // check, a lost default would make the unconnected result a false pass.
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
  EXPECT_EQ(a_binding->connection, nullptr);
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
    EXPECT_NE(b.port_name, "b");
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
  // §23.3.2.2: a port left out of a named connection list is unconnected only
  // when it has no default value. An omitted input that does carry a default
  // (here rst_n) is bound to that default -- the inverse of the explicit empty
  // ".rst_n()" form, which leaves the port unconnected and discards the
  // default.
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
  // The binding points at the declared default expression, not at the high-Z
  // sentinel an unconnected input net would otherwise receive.
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

}  // namespace
