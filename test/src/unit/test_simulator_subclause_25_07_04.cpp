#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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

std::string RunDisabledForkjoin(const char* disable, SimFixture& f) {
  return RunCapture(
      std::string(
          "interface sb;\n"
          "  extern forkjoin task Hit();\n"
          "  modport target(export Hit);\n"
          "endinterface\n"
          "module memMod #(parameter int D = 1)(sb.target a);\n"
          "  task a.Hit(); #(D); $display(\"finished %0d\", D); endtask\n"
          "endmodule\n"
          "module top;\n"
          "  sb s();\n"
          "  memMod #(10) m1(s.target);\n"
          "  memMod #(20) m2(s.target);\n"
          "  initial begin\n"
          "    fork s.Hit(); join_none\n"
          "    #5 ") +
          disable +
          ";\n"
          "    wait fork;\n"
          "    $display(\"done at %0t\", $time);\n"
          "  end\n"
          "endmodule\n",
      f);
}

TEST(InterfaceForkjoinSim, DisableThroughModuleInstanceEndsItsCallAlone) {
  SimFixture f;
  EXPECT_EQ(RunDisabledForkjoin("disable m1.a.Hit", f),
            "finished 20\ndone at 20\n");
}

TEST(InterfaceForkjoinSim, DisableThroughInterfaceInstanceEndsEveryCall) {
  SimFixture f;
  EXPECT_EQ(RunDisabledForkjoin("disable s.Hit", f), "done at 5\n");
}

}  // namespace
