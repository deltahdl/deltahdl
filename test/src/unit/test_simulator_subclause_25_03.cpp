#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §25.3 with §23.3.3.5: each element of an array of interface instances is an
// instance of its own, holding its own members and carrying the parameter
// override its instantiation wrote, here shared with a scalar instance of the
// same item. `vector[3].P` is 100, `plain` and the elements of `pv`,
// instantiated with no override, keep the default 7, and a write to a member
// of an element is read back.
TEST(InterfaceInstanceArraySim, ElementsHoldMembersAndParameters) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface myif #(parameter P = 7); int x; "
                       "endinterface\n"
                       "module top;\n"
                       "  myif #(100) scalar1(), vector[3:0]();\n"
                       "  myif plain();\n"
                       "  myif pv[1:0]();\n"
                       "  initial begin\n"
                       "    vector[2].x = 12;\n"
                       "    plain.x = 3;\n"
                       "    pv[0].x = 5;\n"
                       "    $display(\"P=%0d P=%0d P=%0d x=%0d x=%0d x=%0d\", "
                       "vector[3].P, plain.P, pv[1].P, vector[2].x, plain.x, "
                       "pv[0].x);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "P=100 P=7 P=7 x=12 x=3 x=5\n");
}

// §25.3: an interface port's actual may be a hierarchical reference to an
// interface instance another module instance declares, `h.i`, which joins the
// port to that instance's members. The writer, written before h, and the
// reader, written after it, share h.i's storage, so the value one writes
// through its port is the one the other reads through its own.
TEST(InterfacePortHierRefSim, PortJoinsAnInstanceAnotherModuleDeclares) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc; logic [7:0] a = 1; endinterface\n"
                       "module holder; ifc i(); endmodule\n"
                       "module writer(ifc p); initial p.a = 9; endmodule\n"
                       "module reader(ifc p);\n"
                       "  initial #1 $display(\"x=%0d\", p.a);\n"
                       "endmodule\n"
                       "module top; writer w(h.i); holder h(); reader r(h.i);\n"
                       "endmodule\n",
                       f),
            "x=9\n");
}

// §25.3 with §23.8: a port connected to the module's own interface instance
// through a name starting at the module's name, `top.i`, shares that
// instance's members as one connected to `i` does, so the value written
// through the port is the one top reads (#7353).
TEST(InterfacePortHierRefSim, PortJoinsTheInstanceNamedFromTheModule) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc; logic [7:0] a = 1; endinterface\n"
                       "module writer(ifc p); initial p.a = 9; endmodule\n"
                       "module top; ifc i(); writer w(top.i);\n"
                       "  initial #1 $display(\"x=%0d\", i.a);\n"
                       "endmodule\n",
                       f),
            "x=9\n");
}

// §25.3 with §23.6: an interface port connected in a module below the top
// through a full path from the top, `top.i`, shares the top's instance's
// members, so the value written through the port is the one top reads
// (#7354).
TEST(InterfacePortHierRefSim, PortJoinsTheInstanceNamedFromTheTop) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc; logic [7:0] a = 1; endinterface\n"
                       "module writer(ifc p); initial p.a = 9; endmodule\n"
                       "module mid; writer w(top.i); endmodule\n"
                       "module top; ifc i(); mid m();\n"
                       "  initial #1 $display(\"x=%0d\", i.a);\n"
                       "endmodule\n",
                       f),
            "x=9\n");
}

// §25.3 with §27.4: a module may pass its interface port on to an instance a
// generate block of it holds, which passes it on again. The value the
// innermost instance writes through its port is the one the interface the
// outermost port is connected to holds (#7351).
TEST(InterfacePortIntoGenerateBlockSim,
     PortReachesTheInterfaceThroughTheBlock) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc; logic [7:0] a = 1; endinterface\n"
                       "module leaf(ifc p); initial p.a = 9; endmodule\n"
                       "module mid(ifc p); leaf l(p); endmodule\n"
                       "module outer(ifc p); if (1) begin : gb mid m(p); end\n"
                       "endmodule\n"
                       "module top; ifc i(); outer o(i);\n"
                       "  initial #1 $display(\"x=%0d\", i.a);\n"
                       "endmodule\n",
                       f),
            "x=9\n");
}

}  // namespace
