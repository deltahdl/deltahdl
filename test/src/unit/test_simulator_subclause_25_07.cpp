#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §25.7 with §25.3.2: a module calls the tasks and functions of the interface
// connected to its port by the port's name. `b.hit(10)` runs hit in the
// instance i, so %m names t.i.hit and the count it adds is i's, read through
// the port and from the parent at time 2; `b.tick(o)` takes its delay of 2
// and writes its output back. Before the port's name was resolved to the
// connected instance, neither call ran.
TEST(InterfaceSubroutineSim, CalledThroughNamedInterfacePort) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface bus;\n"
                       "  int calls;\n"
                       "  function void hit(int v); $display(\"hit %0d in "
                       "%m\", v); calls += v; endfunction\n"
                       "  task automatic tick(output int o); #2 o = 9; "
                       "endtask\n"
                       "endinterface\n"
                       "module user2(bus b);\n"
                       "  int o;\n"
                       "  initial begin\n"
                       "    #1 b.hit(10); $display(\"calls via port %0d\", "
                       "b.calls);\n"
                       "    b.tick(o); $display(\"tick o=%0d t=%0t\", o, "
                       "$time);\n"
                       "  end\n"
                       "endmodule\n"
                       "module t;\n"
                       "  bus i();\n"
                       "  user2 v(i);\n"
                       "  initial #2 $display(\"%0d\", i.calls);\n"
                       "endmodule\n",
                       f),
            "hit 10 in t.i.hit\ncalls via port 10\n10\ntick o=9 t=3\n");
}

// §25.7: where a prototype and the declaration both give an argument a
// default, the value a call through the prototype takes is the prototype's.
// b defaults to 9 in f's declaration and to 4 in mp's prototype, and each call
// leaving b without an actual, left out, left empty in order, or by name,
// takes 4.
TEST(InterfaceSubroutineSim, ModportPrototypeDefaultIsTheOneUsed) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface sb;\n"
                       "  function automatic int f(int a, int b = 9); "
                       "return b; endfunction\n"
                       "  modport mp(import function int f(int a, int b = "
                       "4));\n"
                       "endinterface\n"
                       "module m(sb.mp p);\n"
                       "  initial $display(\"v=%0d %0d %0d %0d\", p.f(1), "
                       "p.f(1, ), p.f(.a(1)), p.f(.a(1), .b()));\n"
                       "endmodule\n"
                       "module top; sb s(); m u(s.mp); endmodule\n",
                       f),
            "v=4 4 4 4\n");
}

}  // namespace
