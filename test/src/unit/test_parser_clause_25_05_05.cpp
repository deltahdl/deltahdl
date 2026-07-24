#include "fixture_parser.h"

using namespace delta;

namespace {

// §25.5.5 / Syntax 25-2: modport_clocking_declaration ::= clocking
// clocking_identifier. A clocking item inside a modport parses to a modport
// port flagged as clocking and carrying the clocking block's name.
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

// §25.5.5 / Syntax 25-2: modport_ports_declaration ::= { attribute_instance }
// modport_clocking_declaration. An attribute instance may prefix the clocking
// alternative and the declaration still parses.
TEST(ClockingModportParsing, AttrOnClockingPort) {
  EXPECT_TRUE(
      ParseOk("interface bus(input logic clk);\n"
              "  clocking sb @(posedge clk);\n"
              "  endclocking\n"
              "  modport target((* synthesis *) clocking sb);\n"
              "endinterface\n"));
}

// §25.5.5 / Syntax 25-2: the clocking alternative is one of the
// modport_ports_declaration choices, so a clocking item may sit alongside an
// ordinary simple port in the same modport. Both entries parse, and only the
// second is flagged as clocking.
TEST(ClockingModportParsing, ClockingMixedWithSimplePort) {
  auto r = Parse(
      "interface ifc(input logic clk);\n"
      "  logic a;\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "  modport mp(input a, clocking cb);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_GE(mp->ports.size(), 2u);
  EXPECT_FALSE(mp->ports[0].is_clocking);
  EXPECT_EQ(mp->ports[0].name, "a");
  EXPECT_TRUE(mp->ports[1].is_clocking);
  EXPECT_EQ(mp->ports[1].name, "cb");
}

// §25.5.5 / Syntax 25-2 (negative): modport_clocking_declaration ::= clocking
// clocking_identifier requires an identifier operand after `clocking`. Omitting
// it leaves the production incomplete and must be a parse error.
TEST(ClockingModportParsing, ClockingWithoutIdentifierRejected) {
  auto r = Parse(
      "interface ifc(input logic clk);\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "  modport mp(clocking);\n"
      "endinterface\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
