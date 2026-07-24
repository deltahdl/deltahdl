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

// §25.3.2 input form: the ref access rule applies to a VECTOR variable member,
// not just a scalar one. memMod copies a multi-bit interface variable read
// through its port back onto another member of the same shared instance.
TEST(InterfaceNamedBundleSim, VectorVariableAccessThroughPortSharesInstance) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus;\n"
      "  logic [7:0] addr;\n"
      "  logic [7:0] snoop;\n"
      "endinterface\n"
      "module memMod(simple_bus a);\n"
      "  initial #1 a.snoop = a.addr;\n"
      "endmodule\n"
      "module top;\n"
      "  simple_bus sb_intf();\n"
      "  memMod mem(sb_intf);\n"
      "  initial sb_intf.addr = 8'h3C;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"top.sb_intf.snoop", 0x3Cu}});
}

// §25.3.2 input form: the inout access rule applies to a SCALAR net member as
// well as a vector one. A one-bit interface net driven through the port
// resolves onto the shared net observed on the top-level instance.
TEST(InterfaceNamedBundleSim, ScalarNetDrivenThroughPortReachesSharedNet) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus;\n"
      "  wire valid;\n"
      "endinterface\n"
      "module driver(simple_bus a);\n"
      "  assign a.valid = 1'b1;\n"
      "endmodule\n"
      "module top;\n"
      "  simple_bus sb_intf();\n"
      "  driver d(sb_intf);\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"top.sb_intf.valid", 1u}});
}

// §25.3.2 consumes §23.3.2.2 named port connection: the interface actual is
// bound to the interface port by name, and the ref access rule still holds
// end-to-end (write through the port reaches the shared instance).
TEST(InterfaceNamedBundleSim, VariableRefAccessViaNamedConnection) {
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
      "  memMod mem(.a(sb_intf));\n"
      "  initial sb_intf.req = 1;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"top.sb_intf.gnt", 1u}});
}

// §25.3.2 consumes §23.3.2.3 implicit named port connection (.name): with the
// interface port and the interface instance sharing an identifier, .sb_intf
// binds them, and ref access is observed at run time.
TEST(InterfaceNamedBundleSim, VariableRefAccessViaImplicitConnection) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus;\n"
      "  logic req, gnt;\n"
      "endinterface\n"
      "module memMod(simple_bus sb_intf);\n"
      "  initial #1 sb_intf.gnt = sb_intf.req;\n"
      "endmodule\n"
      "module top;\n"
      "  simple_bus sb_intf();\n"
      "  memMod mem(.sb_intf);\n"
      "  initial sb_intf.req = 1;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"top.sb_intf.gnt", 1u}});
}

// §25.3.2 consumes §23.3.2.4 wildcard port connection (.*): the interface port
// is connected implicitly by the wildcard, and the ref access rule holds
// end-to-end just as with an explicit connection.
TEST(InterfaceNamedBundleSim, VariableRefAccessViaWildcardConnection) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface simple_bus;\n"
      "  logic req, gnt;\n"
      "endinterface\n"
      "module memMod(simple_bus sb_intf);\n"
      "  initial #1 sb_intf.gnt = sb_intf.req;\n"
      "endmodule\n"
      "module top;\n"
      "  simple_bus sb_intf();\n"
      "  memMod mem(.*);\n"
      "  initial sb_intf.req = 1;\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"top.sb_intf.gnt", 1u}});
}

}  // namespace
