#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(InterfaceModport, ModportDeclaration) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic data;\n"
      "  modport master(output data);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->modports[0]->name, "master");
  ASSERT_EQ(r.cu->interfaces[0]->modports[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->modports[0]->ports[0].direction,
            Direction::kOutput);
  EXPECT_EQ(r.cu->interfaces[0]->modports[0]->ports[0].name, "data");
}

TEST(InterfaceModport, ModportWithInputDirection) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic data;\n"
      "  modport slave(input data);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 1u);
  ASSERT_EQ(r.cu->interfaces[0]->modports[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->modports[0]->ports[0].direction,
            Direction::kInput);
}

TEST(InterfaceModport, ModportWithInoutDirection) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic data;\n"
      "  modport bidir(inout data);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 1u);
  ASSERT_EQ(r.cu->interfaces[0]->modports[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->modports[0]->ports[0].direction,
            Direction::kInout);
}

TEST(InterfaceModport, ModportWithMultiplePortsPerDirection) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic a, b, c;\n"
      "  modport master(output a, b, c);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 1u);
  auto& mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 3u);
  EXPECT_EQ(mp->ports[0].direction, Direction::kOutput);
  EXPECT_EQ(mp->ports[0].name, "a");
  EXPECT_EQ(mp->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(mp->ports[1].name, "b");
  EXPECT_EQ(mp->ports[2].direction, Direction::kOutput);
  EXPECT_EQ(mp->ports[2].name, "c");
}

TEST(InterfaceModport, ModportWithMixedDirections) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic a, b, c;\n"
      "  modport mp(input a, output b, inout c);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 1u);
  auto& mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 3u);
  EXPECT_EQ(mp->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(mp->ports[2].direction, Direction::kInout);
}

TEST(InterfaceModport, MultipleModportsInInterface) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic data;\n"
      "  modport master(output data);\n"
      "  modport slave(input data);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 2u);
  EXPECT_EQ(r.cu->interfaces[0]->modports[0]->name, "master");
  EXPECT_EQ(r.cu->interfaces[0]->modports[1]->name, "slave");
}

TEST(InterfaceModport, GenericInterfacePortWithModport) {
  auto r = Parse("module m(interface.master bus); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_TRUE(port.is_interface_port);
  EXPECT_EQ(port.data_type.modport_name, "master");
  EXPECT_EQ(port.name, "bus");
}

TEST(InterfaceModport, NamedInterfacePortWithModport) {
  auto r = Parse("module m(bus_if.slave s); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.data_type.modport_name, "slave");
  EXPECT_EQ(port.name, "s");
}

}  // namespace
