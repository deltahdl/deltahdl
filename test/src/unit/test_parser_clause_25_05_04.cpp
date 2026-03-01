// §25.5.4: Modport expressions

#include "fixture_parser.h"

using namespace delta;

namespace {

// modport_simple_port ::= . port_identifier ( [ expression ] )
TEST(ParserA29, PortExprDotNotation) {
  auto r = Parse(
      "interface bus;\n"
      "  logic [7:0] r;\n"
      "  modport A(output .P(r[3:0]));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_EQ(mp->ports[0].name, "P");
  EXPECT_NE(mp->ports[0].expr, nullptr);
}

TEST(ParserA29, PortExprEmpty) {
  auto r = Parse(
      "interface bus;\n"
      "  modport A(input .P());\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_EQ(mp->ports[0].name, "P");
  EXPECT_EQ(mp->ports[0].expr, nullptr);
}

TEST(ParserA29, PortExprMixedWithSimple) {
  auto r = Parse(
      "interface I;\n"
      "  logic [7:0] r;\n"
      "  bit R;\n"
      "  modport A(output .P(r[3:0]), R);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2u);
  EXPECT_EQ(mp->ports[0].name, "P");
  EXPECT_NE(mp->ports[0].expr, nullptr);
  EXPECT_EQ(mp->ports[1].name, "R");
}

// --- Modport with port expressions (LRM §25.5.4) ---
TEST(ParserSection25, ModportPortExpressionName) {
  auto r = Parse(
      "interface bus;\n"
      "  logic [7:0] bus_data;\n"
      "  modport target(.data(bus_data));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* iface = r.cu->interfaces[0];
  ASSERT_EQ(iface->modports.size(), 1);
  auto* mp = iface->modports[0];
  EXPECT_EQ(mp->name, "target");
}

TEST(ParserSection25, ModportPortExpressionPort) {
  auto r = Parse(
      "interface bus;\n"
      "  logic [7:0] bus_data;\n"
      "  modport target(.data(bus_data));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1);
  EXPECT_EQ(mp->ports[0].name, "data");
  EXPECT_NE(mp->ports[0].expr, nullptr);
}

TEST(ParserSection25, ModportPortExpressionPartSelect) {
  auto r = Parse(
      "interface bus;\n"
      "  logic [7:0] bus_data;\n"
      "  modport target(.data(bus_data[3:0]));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1);
  EXPECT_EQ(mp->ports[0].name, "data");
  EXPECT_NE(mp->ports[0].expr, nullptr);
}

TEST(ParserSection25, ModportMixedDirectionAndExprFirst) {
  auto r = Parse(
      "interface bus;\n"
      "  logic [7:0] bus_data;\n"
      "  logic clk;\n"
      "  modport target(input clk, .data(bus_data[3:0]));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2);
  EXPECT_EQ(mp->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mp->ports[0].name, "clk");
  EXPECT_EQ(mp->ports[0].expr, nullptr);
}

TEST(ParserSection25, ModportMixedDirectionAndExprSecond) {
  auto r = Parse(
      "interface bus;\n"
      "  logic [7:0] bus_data;\n"
      "  logic clk;\n"
      "  modport target(input clk, .data(bus_data[3:0]));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2);
  EXPECT_EQ(mp->ports[1].name, "data");
  EXPECT_NE(mp->ports[1].expr, nullptr);
}

}  // namespace
