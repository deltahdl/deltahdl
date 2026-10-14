// §23.3.3.4 connects an interface port to an interface instance. These cases
// run the connection, so the port reaches the instance's storage and not only
// passes the elaborator's check of the actual.

#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §23.3.2 makes each element of an array of instances an instance of its own,
// so an element of an array of interface instances is a legal actual for an
// interface port, by position and by name, and the port reads that element's
// members: 1 and 2, the values each element was given. The actual was refused
// as naming no interface instance, and once accepted the port was bound to
// nothing and read 0.
TEST(InterfacePortConnection, AnInterfaceArrayElementIsThePortsInstance) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc; logic [1:0] a; endinterface\n"
                       "module user #(int D = 1)(ifc p);\n"
                       "  initial #(D) $display(\"a=%0d\", p.a);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  ifc ia[2]();\n"
                       "  initial begin ia[0].a = 1; ia[1].a = 2; end\n"
                       "  user u0(ia[0]);\n"
                       "  user #(2) u1(.p(ia[1]));\n"
                       "endmodule\n",
                       f),
            "a=1\na=2\n");
}

// A generic interface port, `interface p`, takes the interface of whatever
// instance it is connected to, so an element of an array of interface
// instances gives it that element's interface and storage: the port reads 2,
// what ia[1] holds, not ia[0]'s 1.
TEST(InterfacePortConnection, AGenericPortTakesAnInterfaceArrayElement) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc; logic [1:0] a; endinterface\n"
                       "module user(interface p);\n"
                       "  initial #1 $display(\"a=%0d\", p.a);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  ifc ia[2]();\n"
                       "  initial begin ia[0].a = 1; ia[1].a = 2; end\n"
                       "  user u(ia[1]);\n"
                       "endmodule\n",
                       f),
            "a=2\n");
}

}  // namespace
