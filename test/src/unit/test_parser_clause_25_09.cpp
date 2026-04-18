#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(NetAndVariableTypeParsing, DataTypeVirtualInterface) {
  auto r = Parse(
      "interface my_ifc; endinterface\n"
      "module m; virtual interface my_ifc vif; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kVirtualInterface);
  EXPECT_EQ(item->data_type.type_name, "my_ifc");
}

TEST(InterfaceParsing, VirtualInterfaceDecl) {
  auto r = Parse(
      "module top;\n"
      "  virtual interface simple_bus bus_if;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kVirtualInterface);
  EXPECT_EQ(item->data_type.type_name, "simple_bus");
  EXPECT_EQ(item->name, "bus_if");
}

TEST(InterfaceParsing, VirtualInterfaceNoKeyword) {
  auto r = Parse(
      "module top;\n"
      "  virtual simple_bus bus_if;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kVirtualInterface);
  EXPECT_EQ(item->data_type.type_name, "simple_bus");
  EXPECT_EQ(item->name, "bus_if");
}

TEST(InterfaceParsing, VirtualInterfaceWithModportKind) {
  auto r = Parse(
      "module top;\n"
      "  virtual interface simple_bus.target bus_if;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kVirtualInterface);
  EXPECT_EQ(item->name, "bus_if");
}

TEST(InterfaceParsing, VirtualInterfaceWithModportNames) {
  auto r = Parse(
      "module top;\n"
      "  virtual interface simple_bus.target bus_if;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.type_name, "simple_bus");
  EXPECT_EQ(item->data_type.modport_name, "target");
}

TEST(InterfaceParsing, VirtualInterfaceAssignment) {
  auto r = Parse(
      "module top;\n"
      "  virtual interface simple_bus vif;\n"
      "  initial begin\n"
      "    vif = null;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 2);
  EXPECT_EQ(mod->items[0]->data_type.kind, DataTypeKind::kVirtualInterface);
}

TEST(InterfaceParsing, VirtualInterfaceMultipleDecls) {
  auto r = Parse(
      "module top;\n"
      "  virtual interface bus_if a_if;\n"
      "  virtual bus_if b_if;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 2);
  EXPECT_EQ(mod->items[0]->data_type.kind, DataTypeKind::kVirtualInterface);
  EXPECT_EQ(mod->items[0]->name, "a_if");
  EXPECT_EQ(mod->items[1]->data_type.kind, DataTypeKind::kVirtualInterface);
  EXPECT_EQ(mod->items[1]->name, "b_if");
}

TEST(NetAndVariableTypeParsing, VirtualInterfaceWithModport) {
  auto r = Parse(
      "interface my_ifc;\n"
      "  logic a;\n"
      "  modport mp(input a);\n"
      "endinterface\n"
      "module m; virtual my_ifc.mp vif; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& dt = r.cu->modules[0]->items[0]->data_type;
  EXPECT_EQ(dt.kind, DataTypeKind::kVirtualInterface);
  EXPECT_EQ(dt.modport_name, "mp");
}

TEST(NetAndVariableTypeParsing, VirtualInterfaceWithParams) {
  auto r = Parse(
      "interface my_ifc #(parameter W = 8);\n"
      "endinterface\n"
      "module m; virtual my_ifc#(16) vif; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& dt = r.cu->modules[0]->items[0]->data_type;
  EXPECT_EQ(dt.kind, DataTypeKind::kVirtualInterface);
  EXPECT_FALSE(dt.type_params.empty());
}

TEST(NetAndVariableTypeParsing, VirtualInterfaceWithParamsAndModport) {
  auto r = Parse(
      "interface my_ifc #(parameter W = 8);\n"
      "  logic [W-1:0] a;\n"
      "  modport mp(input a);\n"
      "endinterface\n"
      "module m; virtual my_ifc#(16).mp vif; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& dt = r.cu->modules[0]->items[0]->data_type;
  EXPECT_EQ(dt.kind, DataTypeKind::kVirtualInterface);
  EXPECT_FALSE(dt.type_params.empty());
  EXPECT_EQ(dt.modport_name, "mp");
}

TEST(InterfaceParsing, VirtualInterfaceAsTaskArgument) {
  auto r = Parse(
      "interface simple_bus; endinterface\n"
      "module m;\n"
      "  task do_it(virtual simple_bus v); endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceParsing, VirtualInterfaceAsFunctionArgument) {
  auto r = Parse(
      "interface simple_bus; endinterface\n"
      "module m;\n"
      "  function int do_it(virtual simple_bus v); return 0; endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceParsing, VirtualInterfaceAsMethodArgument) {
  auto r = Parse(
      "interface simple_bus; endinterface\n"
      "class C;\n"
      "  task do_it(virtual simple_bus v); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceParsing, VirtualInterfaceAsClassProperty) {
  auto r = Parse(
      "interface simple_bus; endinterface\n"
      "class C;\n"
      "  virtual simple_bus bus;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceParsing, VirtualInterfaceClassPropertyInitFromNewArg) {
  auto r = Parse(
      "interface simple_bus; endinterface\n"
      "class C;\n"
      "  virtual simple_bus bus;\n"
      "  function new(virtual simple_bus b); bus = b; endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceParsing, VirtualInterfaceEqualityExpression) {
  auto r = Parse(
      "interface simple_bus; endinterface\n"
      "module m;\n"
      "  virtual simple_bus a, b;\n"
      "  initial if (a == b) $display(\"eq\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceParsing, VirtualInterfaceInequalityExpression) {
  auto r = Parse(
      "interface simple_bus; endinterface\n"
      "module m;\n"
      "  virtual simple_bus a;\n"
      "  initial if (a != null) $display(\"init\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
