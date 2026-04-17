#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(FunctionalCoverageParsing, InterfaceClockingWithModport) {
  EXPECT_TRUE(
      ParseOk("interface bus_A (input clk);\n"
              "  logic [15:0] data;\n"
              "  logic write;\n"
              "  clocking cb @(posedge clk);\n"
              "    input data;\n"
              "    output write;\n"
              "  endclocking\n"
              "  modport test (input data, output write, input clk);\n"
              "  modport dut (output data, input write, input clk);\n"
              "endinterface\n"));
}

TEST(ClockingModportParsing, ModportClockingDecl) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic clk;\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "  modport mp(clocking cb);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_GE(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_clocking);
  EXPECT_EQ(mp->ports[0].name, "cb");
}

TEST(ClockingModportParsing, ClockingMixedWithDirectionPorts) {
  auto r = Parse(
      "interface A_Bus(input logic clk);\n"
      "  wire req, gnt;\n"
      "  clocking sb @(posedge clk);\n"
      "  endclocking\n"
      "  modport DUT(input clk, req, output gnt);\n"
      "  modport STB(clocking sb);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* iface = r.cu->interfaces[0];
  ASSERT_EQ(iface->modports.size(), 2u);
  EXPECT_EQ(iface->modports[0]->name, "DUT");
  EXPECT_EQ(iface->modports[1]->name, "STB");
  EXPECT_TRUE(iface->modports[1]->ports[0].is_clocking);
}

TEST(ClockingModportParsing, AttrOnClockingPort) {
  EXPECT_TRUE(
      ParseOk("interface bus(input logic clk);\n"
              "  clocking sb @(posedge clk);\n"
              "  endclocking\n"
              "  modport target((* synthesis *) clocking sb);\n"
              "endinterface\n"));
}

TEST(ClockingModportParsing, ClockingPortNotImportExport) {
  auto r = Parse(
      "interface A_Bus(input logic clk);\n"
      "  clocking sb @(posedge clk);\n"
      "  endclocking\n"
      "  modport STB(clocking sb);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_clocking);
  EXPECT_FALSE(mp->ports[0].is_import);
  EXPECT_FALSE(mp->ports[0].is_export);
  EXPECT_EQ(mp->ports[0].direction, Direction::kNone);
}

TEST(ClockingModportParsing, MultipleClockingPorts) {
  auto r = Parse(
      "interface ifc(input logic clk1, input logic clk2);\n"
      "  clocking cb1 @(posedge clk1); endclocking\n"
      "  clocking cb2 @(posedge clk2); endclocking\n"
      "  modport mp(clocking cb1, clocking cb2);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2u);
  EXPECT_TRUE(mp->ports[0].is_clocking);
  EXPECT_EQ(mp->ports[0].name, "cb1");
  EXPECT_TRUE(mp->ports[1].is_clocking);
  EXPECT_EQ(mp->ports[1].name, "cb2");
}

}  // namespace
