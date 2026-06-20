#include "common/types.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

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
  const auto& bindings = mod->children[0].port_bindings;
  ASSERT_EQ(bindings.size(), 2u);
  EXPECT_EQ(bindings[0].port_name, "a");
  EXPECT_EQ(bindings[0].direction, Direction::kInput);
  EXPECT_EQ(bindings[1].port_name, "b");
  EXPECT_EQ(bindings[1].direction, Direction::kOutput);
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
  // §23.3.2.4: the named connection overrides what .* would have bound, so
  // port a connects to the override expression x rather than the like-named a.
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
  // §23.3.2.4: a named connection mixed with .* overrides the wildcard. Here
  // `.b()` explicitly leaves b unconnected even though a same-named `b` exists
  // in the instantiating scope that .* would otherwise have connected.
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
  // §23.3.2.4 exception 1 (second sentence): when a port has a default and its
  // name is absent from the instantiating scope, .* alone would substitute the
  // default (see DefaultValueUsedWhenNameNotInScope). Adding `.b()` to the .*
  // forces b genuinely unconnected, so the default is NOT used here.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, input logic b = 1'b1);\n"
      "endmodule\n"
      "module top;\n"
      "  logic a;\n"
      "  child u0(.b(), .*);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* inst = &design->top_modules[0]->children[0];
  ASSERT_NE(inst->resolved, nullptr);
  const Expr* b_default = nullptr;
  for (const auto& port : inst->resolved->ports) {
    if (port.name == "b") b_default = port.default_value;
  }
  ASSERT_NE(b_default, nullptr);
  const RtlirPortBinding* b_binding = nullptr;
  for (const auto& binding : inst->port_bindings) {
    if (binding.port_name == "b") b_binding = &binding;
  }
  ASSERT_NE(b_binding, nullptr);
  EXPECT_NE(b_binding->connection, b_default);
}

TEST(WildcardPortConnectionElaboration, DefaultValueUsedWhenNameNotInScope) {
  // §23.3.2.4 exception 1: unlike an explicit .name connection (which errors
  // when the name is absent), .* uses the port's default value for any port
  // whose name does not exist in the instantiating scope.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, input logic b = 1'b1);\n"
      "endmodule\n"
      "module top;\n"
      "  logic a;\n"
      "  child u0(.*);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* inst = &design->top_modules[0]->children[0];
  ASSERT_NE(inst->resolved, nullptr);
  const Expr* b_default = nullptr;
  for (const auto& port : inst->resolved->ports) {
    if (port.name == "b") b_default = port.default_value;
  }
  ASSERT_NE(b_default, nullptr);
  const RtlirPortBinding* b_binding = nullptr;
  for (const auto& binding : inst->port_bindings) {
    if (binding.port_name == "b") b_binding = &binding;
  }
  ASSERT_NE(b_binding, nullptr);
  EXPECT_EQ(b_binding->connection, b_default);
}

TEST(WildcardPortConnectionElaboration,
     WildcardDoesNotReferenceWildcardImport) {
  // §23.3.2.4 exception 2: .* does not create a sufficient reference for a
  // wildcard package import. Even though `sig` is provided by `import pkg::*`,
  // .* does not connect the port to it; the port's default value is used
  // instead, exactly as for a name that is absent from the scope.
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

TEST(WildcardPortConnectionElaboration, MixedStylesInSameParent) {
  EXPECT_TRUE(
      ElabOk("module child(input logic a, output logic b);\n"
             "  assign b = a;\n"
             "endmodule\n"
             "module top;\n"
             "  logic a, b, c, d, e, f;\n"
             "  child u0(a, b);\n"
             "  child u1(.a(c), .b(d));\n"
             "  child u2(.a, .b);\n"
             "  child u3(.*);\n"
             "endmodule\n"));
}

}  // namespace
