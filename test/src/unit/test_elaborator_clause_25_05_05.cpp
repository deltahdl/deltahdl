#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §25.5.5: a modport may name a clocking block declared by its own interface.
// The clocking direction is taken (as with any modport) from the module in
// which the interface becomes a port, so the declaration elaborates cleanly.
TEST(ClockingModportElaboration, SingleClockingPortAccepted) {
  EXPECT_TRUE(
      ElabOk("interface ifc(input logic clk);\n"
             "  clocking cb @(posedge clk); endclocking\n"
             "  modport mp(clocking cb);\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

// §25.5.5 (shall): every clocking block used in a modport declaration must be
// declared by the same interface as the modport itself. Naming a clocking block
// that belongs to a different interface violates that rule and is rejected.
TEST(ClockingModportElaboration, ClockingFromDifferentInterfaceErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface other(input logic clk);\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "endinterface\n"
      "interface ifc(input logic clk);\n"
      "  modport mp(clocking cb);\n"
      "endinterface\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §25.5.5 (shall): the identifier of a clocking item must name a clocking block
// declared by the same interface. The tightest miss is a name the interface
// does declare but as something other than a clocking block (here a variable),
// so it names no clocking block of the interface and is rejected.
TEST(ClockingModportElaboration, ClockingNamingNonClockingItemErrors) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc(input logic clk);\n"
      "  logic cb;\n"
      "  modport mp(clocking cb);\n"
      "endinterface\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §25.5.5 end-to-end: a clocking modport consumes a real clocking block (§14.3)
// whose signals carry directions (§14.9), and the directions are those seen
// from the module in which the interface becomes a port. Build the interface
// with a directional clocking block, expose it through a modport, take that
// modport as a module port, and instantiate the whole thing — it elaborates
// cleanly through the full pipeline with the clocking block driven from real
// source syntax rather than a hand-built stub.
TEST(ClockingModportElaboration, ClockingBlockWithSignalsThroughInterfacePort) {
  EXPECT_TRUE(
      ElabOk("interface bus(input logic clk);\n"
             "  logic req, gnt;\n"
             "  clocking cb @(posedge clk);\n"
             "    input gnt;\n"
             "    output req;\n"
             "  endclocking\n"
             "  modport tb(clocking cb);\n"
             "endinterface\n"
             "module dev(bus.tb b);\n"
             "endmodule\n"
             "module top;\n"
             "  logic clk;\n"
             "  bus b(clk);\n"
             "  dev d(b);\n"
             "endmodule\n"));
}

}  // namespace
