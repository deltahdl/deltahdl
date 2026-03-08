#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(SourceText, InterfaceMultipleItemTypes) {
  auto r = Parse(
      "interface bus_if;\n"
      "  logic [7:0] data;\n"
      "  extern function void validate();\n"
      "  extern forkjoin task run_parallel();\n"
      "  modport master(output data);\n"
      "  modport slave(input data);\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto* ifc = r.cu->interfaces[0];

  ASSERT_GE(ifc->items.size(), 3u);
  EXPECT_EQ(ifc->modports.size(), 2u);
  EXPECT_TRUE(
      HasItemKindNamed(ifc->items, ModuleItemKind::kFunctionDecl, "validate"));
  EXPECT_TRUE(
      HasItemKindNamed(ifc->items, ModuleItemKind::kTaskDecl, "run_parallel"));
}

TEST(InterfaceItemsA16, InterfaceContinuousAssign) {
  auto r = Parse(
      "interface ifc;\n"
      "  wire a, b;\n"
      "  assign a = b;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->interfaces[0]->items, ModuleItemKind::kContAssign));
}

TEST(InterfaceItemsA16, ExternMethodPrototype) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern function void work();\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func =
      FindItemByKind(r.cu->interfaces[0]->items, ModuleItemKind::kFunctionDecl);
  ASSERT_NE(func, nullptr);
  EXPECT_TRUE(func->is_extern);
}

TEST(InterfaceItemsA16, ExternForkjoinTask) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern forkjoin task parallel_run();\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* task =
      FindItemByKind(r.cu->interfaces[0]->items, ModuleItemKind::kTaskDecl);
  ASSERT_NE(task, nullptr);
  EXPECT_TRUE(task->is_extern);
  EXPECT_TRUE(task->is_forkjoin);
}

TEST(InterfaceItemsA16, InterfaceGenerateRegion) {
  auto r = Parse(
      "interface ifc;\n"
      "  generate\n"
      "    wire w;\n"
      "  endgenerate\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceItemsA16, InterfaceNestedProgram) {
  auto r = Parse(
      "interface ifc;\n"
      "  program prg;\n"
      "  endprogram\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceItemsA16, ModportDeclaration) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic data;\n"
      "  modport master(output data);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->interfaces[0]->modports.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->modports[0]->name, "master");
}

TEST(InterfaceItemsA16, InterfaceNestedInterface) {
  auto r = Parse(
      "interface outer_ifc;\n"
      "  interface inner_ifc;\n"
      "  endinterface\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceItemsA16, InterfaceTimeunits) {
  auto r = Parse(
      "interface ifc;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceItemsA16, InterfacePortDecl) {
  auto r = Parse(
      "interface ifc(a, b);\n"
      "  input a;\n"
      "  output b;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceItemsA16, InterfaceAlways) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic clk;\n"
      "  always #5 clk = ~clk;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceItemsA16, InterfaceInitial) {
  auto r = Parse(
      "interface ifc;\n"
      "  initial begin end\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->interfaces[0]->items, ModuleItemKind::kInitialBlock));
}

TEST(InterfaceItemsA16, InterfaceAssertProperty) {
  auto r = Parse(
      "interface ifc;\n"
      "  assert property (@(posedge clk) req |-> ack);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}
