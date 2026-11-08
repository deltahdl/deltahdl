#include <gtest/gtest.h>

#include <string>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_port_connection_elab.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

void ResolveDefaultedPortB(ElabFixture& f, const std::string& connection,
                           const Expr*& b_default,
                           const RtlirPortBinding*& b_binding) {
  auto* design = ElaborateSrc(
      "module child(input logic a, input logic b = 1'b1);\n"
      "endmodule\n"
      "module top;\n"
      "  logic a;\n"
      "  child u0(" +
          connection +
          ");\n"
          "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* inst = &design->top_modules[0]->children[0];
  ASSERT_NE(inst->resolved, nullptr);
  b_default = nullptr;
  for (const auto& port : inst->resolved->ports) {
    if (port.name == "b") b_default = port.default_value;
  }
  ASSERT_NE(b_default, nullptr);
  b_binding = nullptr;
  for (const auto& binding : inst->port_bindings) {
    if (binding.port_name == "b") b_binding = &binding;
  }
  ASSERT_NE(b_binding, nullptr);
}

TEST(WildcardPortConnectionElaboration, WildcardCreatesBindings) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic a, b;\n"
      "  child u0(.*);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_EQ(bindings.size(), 2u);
  EXPECT_NE(bindings[0].connection, nullptr);
  EXPECT_NE(bindings[1].connection, nullptr);
}

TEST(WildcardPortConnectionElaboration, WildcardBindingHasCorrectDirection) {
  ElabFixture f;
  ExpectTwoPortDirections(f, ".*");
}

TEST(WildcardPortConnectionElaboration, WildcardDoesNotCreateImplicitNet) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic a;\n"
      "  child u0(.*);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  for (const auto& net : mod->nets) {
    EXPECT_NE(net.name, "a");
  }
}

TEST(WildcardPortConnectionElaboration, NamedOverrideWithWildcard) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, input logic b, output logic c);\n"
      "  assign c = a & b;\n"
      "endmodule\n"
      "module top;\n"
      "  logic a, b, c, x;\n"
      "  child u0(.a(x), .*);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_GE(bindings.size(), 3u);
  const RtlirPortBinding* a_binding = nullptr;
  for (const auto& binding : bindings) {
    if (binding.port_name == "a") a_binding = &binding;
  }
  ASSERT_NE(a_binding, nullptr);
  ASSERT_NE(a_binding->connection, nullptr);
  EXPECT_EQ(a_binding->connection->kind, ExprKind::kIdentifier);
  EXPECT_EQ(a_binding->connection->text, "x");
}

TEST(WildcardPortConnectionElaboration, EmptyPortOverrideDisconnectsPort) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  logic a, b;\n"
      "  child u0(.b(), .*);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* inst = &design->top_modules[0]->children[0];
  const RtlirPortBinding* b_binding = nullptr;
  for (const auto& binding : inst->port_bindings) {
    if (binding.port_name == "b") b_binding = &binding;
  }
  ASSERT_NE(b_binding, nullptr);
  EXPECT_EQ(b_binding->connection, nullptr);
}

TEST(WildcardPortConnectionElaboration, EmptyPortOverrideSuppressesDefault) {
  ElabFixture f;
  const Expr* b_default = nullptr;
  const RtlirPortBinding* b_binding = nullptr;
  ResolveDefaultedPortB(f, ".b(), .*", b_default, b_binding);
  EXPECT_NE(b_binding->connection, b_default);
}

TEST(WildcardPortConnectionElaboration, DefaultValueUsedWhenNameNotInScope) {
  ElabFixture f;
  const Expr* b_default = nullptr;
  const RtlirPortBinding* b_binding = nullptr;
  ResolveDefaultedPortB(f, ".*", b_default, b_binding);
  EXPECT_EQ(b_binding->connection, b_default);
}

TEST(WildcardPortConnectionElaboration,
     WildcardDoesNotReferenceWildcardImport) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  logic sig;\n"
      "endpackage\n"
      "module child(input logic sig = 1'b1, output logic out);\n"
      "  assign out = sig;\n"
      "endmodule\n"
      "module top;\n"
      "  import pkg::*;\n"
      "  logic out;\n"
      "  child u0(.*);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* inst = &design->top_modules[0]->children[0];
  ASSERT_NE(inst->resolved, nullptr);
  const Expr* sig_default = nullptr;
  for (const auto& port : inst->resolved->ports) {
    if (port.name == "sig") sig_default = port.default_value;
  }
  ASSERT_NE(sig_default, nullptr);
  const RtlirPortBinding* sig_binding = nullptr;
  for (const auto& binding : inst->port_bindings) {
    if (binding.port_name == "sig") sig_binding = &binding;
  }
  ASSERT_NE(sig_binding, nullptr);
  EXPECT_EQ(sig_binding->connection, sig_default);
}

TEST(WildcardPortConnectionElaboration, WildcardBindsInoutPort) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(inout [7:0] bus, output logic [7:0] mon);\n"
      "  assign mon = bus;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] bus;\n"
      "  logic [7:0] mon;\n"
      "  child u0(.*);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* inst = &design->top_modules[0]->children[0];
  const RtlirPortBinding* bus_binding = nullptr;
  for (const auto& binding : inst->port_bindings) {
    if (binding.port_name == "bus") bus_binding = &binding;
  }
  ASSERT_NE(bus_binding, nullptr);
  EXPECT_EQ(bus_binding->direction, Direction::kInout);
  EXPECT_NE(bus_binding->connection, nullptr);
}

TEST(WildcardPortConnectionElaboration, MixedStylesInSameParent) {
  EXPECT_TRUE(
      ElabOk("module child(input logic a, input logic b);\n"
             "endmodule\n"
             "module top;\n"
             "  logic a, b, c, d;\n"
             "  child u0(a, b);\n"
             "  child u1(.a(c), .b(d));\n"
             "  child u2(.a, .b);\n"
             "  child u3(.*);\n"
             "endmodule\n"));
}

TEST(WildcardPortConnectionElaboration,
     SameWidthButNonEquivalentTypesAreReported) {
  ElabFixture f;
  ElaborateSrc(
      "module leaf(input var shortint p, input var byte q,\n"
      "            input var integer r);\n"
      "endmodule\n"
      "module top;\n"
      "  logic signed [15:0] p;\n"
      "  bit [7:0] q;\n"
      "  logic signed [31:0] r;\n"
      "  leaf l(.*);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'.p' requires equivalent data types", 8,
                            "23.3.2.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'.q' requires equivalent data types", 8,
                            "23.3.2.4"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "'.r'", 8, "23.3.2.4"));
}

}  // namespace
