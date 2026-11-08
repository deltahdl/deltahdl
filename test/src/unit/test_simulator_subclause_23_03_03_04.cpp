#include <gtest/gtest.h>

#include "fixture_simulator.h"

using namespace delta;

namespace {

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
