#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(GenericInterfaceReference, SinglePort) {
  auto r = Parse("module m(interface bus); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_TRUE(port.is_interface_port);
  EXPECT_EQ(port.name, "bus");
}

TEST(GenericInterfaceReference, MultiplePorts) {
  auto r = Parse("module cpuMod(interface d, interface j); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_TRUE(r.cu->modules[0]->ports[0].is_interface_port);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "d");
  EXPECT_TRUE(r.cu->modules[0]->ports[1].is_interface_port);
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "j");
}

TEST(GenericInterfaceReference, MixedWithScalarPorts) {
  auto r = Parse("module memMod(interface a, input logic clk); endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_TRUE(r.cu->modules[0]->ports[0].is_interface_port);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_FALSE(r.cu->modules[0]->ports[1].is_interface_port);
  EXPECT_EQ(r.cu->modules[0]->ports[1].direction, Direction::kInput);
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "clk");
}

TEST(GenericInterfaceReference, NonAnsiDeclarationIsError) {
  auto r = Parse(
      "module memMod(a, clk);\n"
      "  input interface a;\n"
      "  input logic clk;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
