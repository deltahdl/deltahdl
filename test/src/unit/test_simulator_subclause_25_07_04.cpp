#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §25.7.4: an extern forkjoin task called through the interface runs every
// definition its connected modules export, as a fork-join of their enables,
// so countTargets from the interface's own initial procedure counts both
// memMod instances. A call through one instance's path,
// `top.mem2.a.Read(200)`, runs that instance's definition alone, whose
// address range holds 200, and returns after its delay of 10. Before the
// definitions were registered, the count was 0 and the call took no time.
TEST(InterfaceForkjoinSim, CallRunsEveryDefinitionAndOneByPath) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface simple_bus;\n"
                       "  int targets = 0;\n"
                       "  logic [7:0] data;\n"
                       "  extern forkjoin task countTargets();\n"
                       "  extern forkjoin task Read(input logic [7:0] "
                       "raddr);\n"
                       "  modport target(ref targets, ref data, export "
                       "countTargets, export Read);\n"
                       "  initial begin\n"
                       "    #1 countTargets;\n"
                       "    $display(\"number of targets = %0d\", targets);\n"
                       "  end\n"
                       "endinterface\n"
                       "module memMod #(parameter int minaddr = 0, maxaddr = "
                       "0)(simple_bus.target a);\n"
                       "  task a.countTargets(); a.targets++; endtask\n"
                       "  task a.Read(input logic [7:0] raddr);\n"
                       "    if (raddr >= minaddr && raddr <= maxaddr) #10 "
                       "$display(\"read %0d t=%0t\", raddr, $time);\n"
                       "  endtask\n"
                       "endmodule\n"
                       "module top;\n"
                       "  simple_bus sb_intf();\n"
                       "  memMod #(0, 127) mem1(sb_intf.target);\n"
                       "  memMod #(128, 255) mem2(sb_intf.target);\n"
                       "  initial begin\n"
                       "    #2 top.mem2.a.Read(200);\n"
                       "    $display(\"only one t=%0t\", $time);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "number of targets = 2\nread 200 t=12\nonly one t=12\n");
}

// §25.7.4: the definitions run at once, not one after another, so a call
// whose two definitions each wait 5 returns at time 5, not 10.
TEST(InterfaceForkjoinSim, DefinitionsRunConcurrently) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface bus;\n"
                       "  extern forkjoin task wait5();\n"
                       "  modport target(export wait5);\n"
                       "endinterface\n"
                       "module tgt(bus.target a);\n"
                       "  task a.wait5(); #5; endtask\n"
                       "endmodule\n"
                       "module top;\n"
                       "  bus b();\n"
                       "  tgt t1(b.target), t2(b.target);\n"
                       "  initial begin\n"
                       "    b.wait5();\n"
                       "    $display(\"t=%0t\", $time);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "t=5\n");
}

// §25.7.4: a call of an extern forkjoin task that no connected module
// defines is a run-time error, after which the call returns with no effect.
// Before this the call returned with no report.
TEST(InterfaceForkjoinSim, CallWithNoDefinitionIsReported) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface simple_bus;\n"
                       "  int targets = 0;\n"
                       "  extern forkjoin task countTargets();\n"
                       "  modport target(ref targets, export countTargets);\n"
                       "endinterface\n"
                       "module top;\n"
                       "  simple_bus sb_intf();\n"
                       "  initial begin\n"
                       "    sb_intf.countTargets;\n"
                       "    $display(\"after t=%0t\", $time);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "after t=0\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "is defined by no module", 9,
                            "25.7.4"));
}

}  // namespace
