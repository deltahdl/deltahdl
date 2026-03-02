// §25.9: Virtual interfaces

#include "fixture_parser.h"

using namespace delta;

namespace {

// virtual [interface] interface_identifier [parameter_value_assignment]
//   [. modport_identifier]
TEST(ParserA221, DataTypeVirtualInterface) {
  auto r = Parse(
      "interface my_ifc; endinterface\n"
      "module m; virtual interface my_ifc vif; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kVirtualInterface);
  EXPECT_EQ(item->data_type.type_name, "my_ifc");
}

// --- Virtual interface (LRM §25.9) ---
TEST(ParserSection25, VirtualInterfaceDecl) {
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

TEST(ParserSection25, VirtualInterfaceNoKeyword) {
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

TEST(ParserSection25, VirtualInterfaceWithModportKind) {
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

TEST(ParserSection25, VirtualInterfaceWithModportNames) {
  auto r = Parse(
      "module top;\n"
      "  virtual interface simple_bus.target bus_if;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.type_name, "simple_bus");
  EXPECT_EQ(item->data_type.modport_name, "target");
}

// --- Virtual interface with parameter (LRM §25.9) ---
TEST(ParserSection25, VirtualInterfaceAssignment) {
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

}  // namespace
