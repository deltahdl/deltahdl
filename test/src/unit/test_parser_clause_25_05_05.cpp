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

}  // namespace
