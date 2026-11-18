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

TEST(InterfaceForkjoinSim, TwoModuleTypesRunTogetherThroughAnImportingPort) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface sb;\n"
                       "  int hits = 0;\n"
                       "  extern forkjoin task bump(input int n);\n"
                       "  modport target(export bump);\n"
                       "  modport initiator(import task bump(input int n));\n"
                       "endinterface\n"
                       "module ma(interface a);\n"
                       "  task a.bump(input int n);\n"
                       "    #2 a.hits += n;\n"
                       "    $display(\"ma at %0t\", $time);\n"
                       "  endtask\n"
                       "endmodule\n"
                       "module mb(interface a);\n"
                       "  task a.bump(input int n);\n"
                       "    #3 a.hits += 10 * n;\n"
                       "    $display(\"mb at %0t\", $time);\n"
                       "  endtask\n"
                       "endmodule\n"
                       "module cpu(sb.initiator b);\n"
                       "  initial begin\n"
                       "    b.bump(1);\n"
                       "    $display(\"back at %0t\", $time);\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  sb s();\n"
                       "  ma u1(s.target);\n"
                       "  mb u2(s.target);\n"
                       "  cpu c(s);\n"
                       "  initial #4 $display(\"hits %0d\", s.hits);\n"
                       "endmodule\n",
                       f),
            "ma at 2\nmb at 3\nback at 3\nhits 11\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(InterfaceForkjoinSim,
     AnUndefinedCallFromThePortOrTheInterfaceReturnsAtOnce) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface sb;\n"
                       "  extern forkjoin task none();\n"
                       "  modport initiator(import task none());\n"
                       "  initial begin\n"
                       "    #1 none;\n"
                       "    $display(\"interface back at %0t\", $time);\n"
                       "  end\n"
                       "endinterface\n"
                       "module cpu(sb.initiator b);\n"
                       "  initial begin\n"
                       "    #2 b.none;\n"
                       "    $display(\"port back at %0t\", $time);\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  sb s();\n"
                       "  cpu c(s);\n"
                       "endmodule\n",
                       f),
            "interface back at 1\nport back at 2\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "is defined by no module", 5,
                            "25.7.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "is defined by no module", 11,
                            "25.7.4"));
}

std::string RunTheSectionsExample(const std::string& interrupt) {
  SimFixture f;
  std::string out = RunCapture(
      std::string("interface simple_bus(input logic clk);\n"
                  "  logic [7:0] data;\n"
                  "  int targets = 0;\n"
                  "  extern forkjoin task countTargets();\n"
                  "  extern forkjoin task Read(input logic [7:0] raddr);\n"
                  "  extern forkjoin task Write(input logic [7:0] waddr);\n"
                  "  modport target(input clk, ref data, targets,\n"
                  "    export Read, Write, countTargets);\n"
                  "  modport initiator(input clk, ref data,\n"
                  "    import task Read(input logic [7:0] raddr),\n"
                  "           task Write(input logic [7:0] waddr));\n"
                  "  initial begin\n"
                  "    targets = 0;\n"
                  "    countTargets;\n"
                  "    $display(\"number of targets = %0d\", targets);\n"
                  "  end\n"
                  "endinterface: simple_bus\n"
                  "module memMod #(parameter int minaddr = 0, maxaddr = 0)\n"
                  "    (interface a);\n"
                  "  logic avail = 1;\n"
                  "  logic [7:0] mem[255:0];\n"
                  "  task a.countTargets();\n"
                  "    a.targets++;\n"
                  "  endtask\n"
                  "  task a.Read(input logic [7:0] raddr);\n"
                  "    if (raddr >= minaddr && raddr <= maxaddr) begin\n"
                  "      avail = 0;\n"
                  "      #10 a.data = mem[raddr];\n"
                  "      avail = 1;\n"
                  "    end\n"
                  "  endtask\n"
                  "  task a.Write(input logic [7:0] waddr);\n"
                  "    if (waddr >= minaddr && waddr <= maxaddr) begin\n"
                  "      avail = 0;\n"
                  "      #10 mem[waddr] = a.data;\n"
                  "      avail = 1;\n"
                  "    end\n"
                  "  endtask\n"
                  "endmodule\n"
                  "module cpuMod(interface b);\n"
                  "  initial begin\n"
                  "    #5 b.data = 8'h11;\n"
                  "    b.Write(8'h02);\n"
                  "    $display(\"%0t wrote %h\", $time, b.data);\n"
                  "    #5 b.data = 8'h00;\n"
                  "    b.Read(8'h02);\n"
                  "    $display(\"%0t read %h\", $time, b.data);\n"
                  "    #1 b.data = 8'h22;\n"
                  "    b.Write(8'h82);\n"
                  "    $display(\"%0t wrote %h\", $time, b.data);\n"
                  "    #1 b.Read(8'h02);\n"
                  "    $display(\"%0t read %h\", $time, b.data);\n"
                  "    b.Read(8'h82);\n"
                  "    $display(\"%0t read %h\", $time, b.data);\n"
                  "  end\n"
                  "endmodule\n"
                  "module top;\n"
                  "  logic clk = 0;\n") +
          interrupt +
          "  simple_bus sb_intf(clk);\n"
          "  memMod #(0, 127) mem1(sb_intf.target);\n"
          "  memMod #(128, 255) mem2(sb_intf.target);\n"
          "  cpuMod cpu(sb_intf.initiator);\n"
          "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  return out;
}

constexpr const char* kTheSectionsRun =
    "number of targets = 2\n"
    "15 wrote 11\n"
    "mem1 was interrupted\n"
    "28 read 00\n"
    "mem1 was interrupted\n"
    "mem2 was interrupted\n"
    "38 wrote 22\n"
    "49 read 11\n"
    "59 read xx\n";

TEST(InterfaceForkjoinSim, TheSectionsInterruptsEndTheCallsTheyName) {
  EXPECT_EQ(RunTheSectionsExample(
                "  initial begin\n"
                "    #28;\n"
                "    disable mem1.a.Read;\n"
                "    disable sb_intf.Write;\n"
                "    if (mem1.avail == 0) $display(\"mem1 was interrupted\");\n"
                "    if (mem2.avail == 0) $display(\"mem2 was interrupted\");\n"
                "    #10;\n"
                "    disable mem1.a.Read;\n"
                "    disable sb_intf.Write;\n"
                "    if (mem1.avail == 0) $display(\"mem1 was interrupted\");\n"
                "    if (mem2.avail == 0) $display(\"mem2 was interrupted\");\n"
                "  end\n"),
            kTheSectionsRun);
}

TEST(InterfaceForkjoinSim,
     DISABLED_TheSectionsInterruptFunctionEndsTheCallsItNames) {
  EXPECT_EQ(RunTheSectionsExample(
                "  function void interrupt();\n"
                "    disable mem1.a.Read;\n"
                "    disable sb_intf.Write;\n"
                "    if (mem1.avail == 0) $display(\"mem1 was interrupted\");\n"
                "    if (mem2.avail == 0) $display(\"mem2 was interrupted\");\n"
                "  endfunction\n"
                "  initial begin\n"
                "    #28 interrupt();\n"
                "    #10 interrupt();\n"
                "  end\n"),
            kTheSectionsRun);
}

}  // namespace
