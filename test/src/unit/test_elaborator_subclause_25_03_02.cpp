

#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "parser/ast_expr.h"

namespace {

TEST(InterfaceNamedBundle, InterfaceWithVariablesElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc;\n"
      "  logic req, gnt;\n"
      "  logic [7:0] addr, data;\n"
      "endinterface\n",
      f, "ifc");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterfaceNamedBundle, ModuleWithInterfacePortElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus(input logic clk);\n"
      "  logic req, gnt;\n"
      "endinterface\n"
      "module memMod(simple_bus a);\n"
      "  logic avail;\n"
      "  always @(posedge a.clk) a.gnt <= a.req & avail;\n"
      "endmodule\n",
      f, "memMod");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterfaceNamedBundle, TopBindsInterfaceToModulePositionally) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus(input logic clk);\n"
      "  logic req, gnt;\n"
      "endinterface\n"
      "module memMod(simple_bus a, input logic clk);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  memMod mem(sb_intf, clk);\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 2u);
  EXPECT_EQ(top->children[0].module_name, "simple_bus");
  EXPECT_EQ(top->children[0].inst_name, "sb_intf");
  EXPECT_NE(top->children[0].resolved, nullptr);
  EXPECT_EQ(top->children[1].module_name, "memMod");
  EXPECT_EQ(top->children[1].inst_name, "mem");
  EXPECT_NE(top->children[1].resolved, nullptr);
}

TEST(InterfaceNamedBundle, TopBindsInterfaceToModuleByName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus(input logic clk);\n"
      "  logic req;\n"
      "endinterface\n"
      "module cpuMod(simple_bus b, input logic clk);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  cpuMod cpu(.b(sb_intf), .clk(clk));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 2u);
  EXPECT_EQ(top->children[1].module_name, "cpuMod");
  EXPECT_NE(top->children[1].resolved, nullptr);
}

TEST(InterfaceNamedBundle, TopBindsInterfaceToModuleImplicitly) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus(input logic clk);\n"
      "  logic req;\n"
      "endinterface\n"
      "module memMod(simple_bus sb_intf, input logic clk);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  memMod mem(.*);\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 2u);
  EXPECT_EQ(top->children[1].module_name, "memMod");
  EXPECT_NE(top->children[1].resolved, nullptr);
}

// §25.3.2 with §23.3.2.3: the implicit named form `.iface` is the named
// connection `.iface(iface)`, and the name an interface port is connected
// to by that form may be an interface instance of the instantiating scope as
// well as a signal -- §23.3.2.3 asks only that the name be declared there, and
// `test_bus iface();` declares it. This is the shape of sv-tests'
// 25.3-interface.sv, which was reported as "requires signal 'iface' to be
// declared" (#4355): the report asked the module's signals alone about the
// name. The binding's connection is the identifier the instance goes by, as
// the explicit form binds it.
TEST(InterfaceNamedBundle, TopBindsInterfaceToModuleByImplicitName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface test_bus;\n"
      "  logic test_pad;\n"
      "endinterface: test_bus\n"
      "module sub(test_bus iface);\n"
      "endmodule\n"
      "module top;\n"
      "  test_bus iface();\n"
      "  sub sub (.iface);\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  ASSERT_EQ(top->children.size(), 2u);
  const auto& sub = top->children[1];
  EXPECT_EQ(sub.module_name, "sub");
  ASSERT_EQ(sub.port_bindings.size(), 1u);
  EXPECT_EQ(sub.port_bindings[0].port_name, "iface");
  ASSERT_NE(sub.port_bindings[0].connection, nullptr);
  EXPECT_EQ(sub.port_bindings[0].connection->kind, ExprKind::kIdentifier);
  EXPECT_EQ(sub.port_bindings[0].connection->text, "iface");
}

}  // namespace
