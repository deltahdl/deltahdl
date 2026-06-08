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

}
