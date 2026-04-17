#include "fixture_elaborator.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(InterfaceDefinitions, EmptyInterfaceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc("interface ifc; endinterface\n", f, "ifc");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(InterfaceInstantiationGrammar, ElaborationInterfaceInstInModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface my_bus(input logic clk, input logic rst);\n"
      "endinterface\n"
      "module top;\n"
      "  logic clk, rst;\n"
      "  my_bus bus0(.clk(clk), .rst(rst));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].module_name, "my_bus");
  EXPECT_EQ(top->children[0].inst_name, "bus0");
  EXPECT_NE(top->children[0].resolved, nullptr);
}

TEST(InterfaceInstantiationGrammar, ElaborationInterfaceInsideInterface) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface inner_if(input logic sig);\n"
      "endinterface\n"
      "interface outer_if;\n"
      "  logic sig;\n"
      "  inner_if u0(.sig(sig));\n"
      "endinterface\n"
      "module top;\n"
      "  outer_if oi();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].module_name, "outer_if");
  auto* outer = top->children[0].resolved;
  ASSERT_NE(outer, nullptr);
  ASSERT_GE(outer->children.size(), 1u);
  EXPECT_EQ(outer->children[0].module_name, "inner_if");
  EXPECT_NE(outer->children[0].resolved, nullptr);
}

TEST(InterfaceInstantiationGrammar, ElaborationInterfaceInstPortBindings) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface simple_if(input logic data);\n"
      "endinterface\n"
      "module top;\n"
      "  logic d;\n"
      "  simple_if u0(.data(d));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_GE(top->children[0].port_bindings.size(), 1u);
  EXPECT_EQ(top->children[0].port_bindings[0].port_name, "data");
}

TEST(InterfaceInstantiationGrammar, ElaborationMultipleInstances) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface my_if(input logic clk);\n"
      "endinterface\n"
      "module top;\n"
      "  logic clk;\n"
      "  my_if u0(.clk(clk)), u1(.clk(clk));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 2u);
  EXPECT_EQ(top->children[0].module_name, "my_if");
  EXPECT_EQ(top->children[0].inst_name, "u0");
  EXPECT_NE(top->children[0].resolved, nullptr);
  EXPECT_EQ(top->children[1].module_name, "my_if");
  EXPECT_EQ(top->children[1].inst_name, "u1");
  EXPECT_NE(top->children[1].resolved, nullptr);
}

TEST(InterfaceInstantiationGrammar, ElaborationUnresolvedInterface) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top;\n"
      "  nonexistent_if u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].resolved, nullptr);
}

TEST(InterfaceDefinitions, ModuleDeclInsideInterfaceIsError) {
  ElabFixture f;
  Elaborate(
      "interface ifc;\n"
      "  module bad;\n"
      "  endmodule\n"
      "endinterface\n"
      "module top;\n"
      "  ifc u0();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

TEST(InterfaceDefinitions, ModuleInstantiationInsideInterfaceIsError) {
  ElabFixture f;
  Elaborate(
      "module sub;\n"
      "endmodule\n"
      "interface ifc;\n"
      "  sub u0();\n"
      "endinterface\n"
      "module top;\n"
      "  ifc u1();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

TEST(InterfaceDefinitions, NotImplicitlyInstantiated) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface inner;\n"
      "endinterface\n"
      "module top;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_TRUE(design->top_modules[0]->children.empty());
}

TEST(InterfaceDefinitions, NestedInterfaceNotImplicitlyInstantiated) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface outer;\n"
      "  interface inner;\n"
      "  endinterface\n"
      "endinterface\n"
      "module top;\n"
      "  outer o0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  auto* outer = top->children[0].resolved;
  ASSERT_NE(outer, nullptr);
  EXPECT_TRUE(outer->children.empty());
}

}  // namespace
