#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §25.3.2: when an interface is referenced as a port, the variables in it are
// accessed by reference. The reference is symmetric: a value placed on an
// interface variable from the instantiating scope is observed when the module
// reads it through its interface port, and a write the module performs through
// the port reaches the shared interface instance. Here memMod reads a.req (set
// on sb_intf in top) and writes a.gnt; both touch the single sb_intf instance.
TEST(InterfaceNamedBundleSim, VariableAccessThroughPortSharesInstance) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus;\n"
      "  logic req, gnt;\n"
      "endinterface\n"
      "module memMod(simple_bus a);\n"
      "  initial #1 a.gnt = a.req;\n"
      "endmodule\n"
      "module top;\n"
      "  simple_bus sb_intf();\n"
      "  memMod mem(sb_intf);\n"
      "  initial sb_intf.req = 1;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"top.sb_intf.gnt", 1u}});
}

// §25.3.2: the nets in an interface referenced as a port have inout access. A
// net driven through the interface port by a continuous assignment resolves
// onto the shared interface net, observable on the instance declared in top.
TEST(InterfaceNamedBundleSim, NetDrivenThroughPortReachesSharedNet) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus;\n"
      "  wire [7:0] data;\n"
      "endinterface\n"
      "module driver(simple_bus a);\n"
      "  assign a.data = 8'hA5;\n"
      "endmodule\n"
      "module top;\n"
      "  simple_bus sb_intf();\n"
      "  driver d(sb_intf);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"top.sb_intf.data", 0xA5u}});
}

}
