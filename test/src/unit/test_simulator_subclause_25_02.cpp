#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string RunWithoutErrors(const std::string& src) {
  SimFixture f;
  auto out = RunCapture(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  return out;
}

TEST(InterfaceOverviewSim, AModuleReachesTheBundledNetsAndVariablesByOnePort) {
  EXPECT_EQ(
      RunWithoutErrors("interface bus;\n"
                       "  logic [7:0] data;\n"
                       "  wire ready;\n"
                       "endinterface\n"
                       "module drv(bus b);\n"
                       "  assign b.ready = 1'b1;\n"
                       "  initial #1 b.data = 8'd17;\n"
                       "endmodule\n"
                       "module mon(bus b);\n"
                       "  initial #2 $display(\"%0d %b\", b.data, b.ready);\n"
                       "endmodule\n"
                       "module top;\n"
                       "  bus b();\n"
                       "  drv d(b);\n"
                       "  mon m(b);\n"
                       "endmodule\n"),
      "17 1\n");
}

TEST(InterfaceOverviewSim, AnInterfaceTakesParametersConstantsAndAPassedType) {
  EXPECT_EQ(RunWithoutErrors(
                "interface bus #(parameter int W = 4, type T = byte);\n"
                "  localparam int Twice = 2 * W;\n"
                "  logic [W-1:0] data;\n"
                "  T tag;\n"
                "endinterface\n"
                "module top;\n"
                "  bus #(.W(12), .T(shortint)) b();\n"
                "  initial begin\n"
                "    b.data = '1;\n"
                "    b.tag = -2;\n"
                "    $display(\"%0d %0d %0d %0d\", b.data, b.Twice, b.tag,\n"
                "             $bits(b.tag));\n"
                "  end\n"
                "endmodule\n"),
            "4095 24 -2 16\n");
}

TEST(InterfaceOverviewSim, AnInterfaceDeclaresATypeItsMembersUse) {
  EXPECT_EQ(RunWithoutErrors(
                "interface bus;\n"
                "  typedef struct packed { logic [3:0] hi, lo; } pair_t;\n"
                "  pair_t p;\n"
                "endinterface\n"
                "module top;\n"
                "  bus b();\n"
                "  initial begin\n"
                "    b.p = 8'hA5;\n"
                "    $display(\"%h %h\", b.p.hi, b.p.lo);\n"
                "  end\n"
                "endmodule\n"),
            "a 5\n");
}

TEST(InterfaceOverviewSim, AConnectedModuleCallsTheInterfacesSubroutines) {
  EXPECT_EQ(RunWithoutErrors("interface bus;\n"
                             "  logic [7:0] data;\n"
                             "  task automatic put(input logic [7:0] v);\n"
                             "    #1 data = v;\n"
                             "  endtask\n"
                             "  function automatic logic [7:0] peek();\n"
                             "    return data + 8'd1;\n"
                             "  endfunction\n"
                             "endinterface\n"
                             "module user(bus b);\n"
                             "  initial begin\n"
                             "    b.put(8'd40);\n"
                             "    $display(\"%0d at %0t\", b.peek(), $time);\n"
                             "  end\n"
                             "endmodule\n"
                             "module top;\n"
                             "  bus b();\n"
                             "  user u(b);\n"
                             "endmodule\n"),
            "41 at 1\n");
}

TEST(InterfaceOverviewSim, AnotherInterfaceWithTheSameMembersServesTheModule) {
  EXPECT_EQ(
      RunWithoutErrors("interface fast;\n"
                       "  int count;\n"
                       "  task automatic step(); count += 1; endtask\n"
                       "endinterface\n"
                       "interface slow;\n"
                       "  int count;\n"
                       "  task automatic step(); #5 count += 10; endtask\n"
                       "endinterface\n"
                       "module user(interface i);\n"
                       "  initial begin\n"
                       "    i.step();\n"
                       "    i.step();\n"
                       "    $display(\"%m %0d at %0t\", i.count, $time);\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  fast f();\n"
                       "  slow s();\n"
                       "  user uf(f);\n"
                       "  user us(s);\n"
                       "endmodule\n"),
      "top.uf 2 at 0\ntop.us 20 at 10\n");
}

TEST(InterfaceOverviewSim, AModportGivesTheDirectionsSeenFromTheModule) {
  EXPECT_EQ(
      RunWithoutErrors("interface bus;\n"
                       "  logic [7:0] req, gnt;\n"
                       "  modport host(output req, input gnt);\n"
                       "  modport dev(input req, output gnt);\n"
                       "endinterface\n"
                       "module h(bus.host b);\n"
                       "  initial #1 b.req = 8'd3;\n"
                       "  initial #3 $display(\"host sees %0d\", b.gnt);\n"
                       "endmodule\n"
                       "module d(bus.dev b);\n"
                       "  initial #2 b.gnt = b.req * 8'd2;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  bus b();\n"
                       "  h hi(b);\n"
                       "  d di(b);\n"
                       "endmodule\n"),
      "host sees 6\n");
}

TEST(InterfaceOverviewSim, AnInterfaceHoldsProcessesAndContinuousAssignments) {
  EXPECT_EQ(RunWithoutErrors(
                "interface bus;\n"
                "  logic [7:0] data;\n"
                "  wire [7:0] doubled;\n"
                "  assign doubled = data * 8'd2;\n"
                "  always @(data) if ($time > 0)\n"
                "    $display(\"checker sees %0d %0d\", data, doubled);\n"
                "  initial data = 8'd1;\n"
                "endinterface\n"
                "module top;\n"
                "  bus b();\n"
                "  initial #4 b.data = 8'd9;\n"
                "  initial #5 $display(\"top sees %0d\", b.doubled);\n"
                "endmodule\n"),
            "checker sees 9 18\ntop sees 18\n");
}

TEST(InterfaceOverviewSim, AnExportedTaskDefinedInOneModuleIsCalledInAnother) {
  EXPECT_EQ(
      RunWithoutErrors("interface bus;\n"
                       "  logic [7:0] data;\n"
                       "  modport provider(output data, export task send(input "
                       "logic [7:0] v));\n"
                       "  modport client(input data, import task send(input "
                       "logic [7:0] v));\n"
                       "endinterface\n"
                       "module prov(bus.provider b);\n"
                       "  task b.send(input logic [7:0] v);\n"
                       "    #2 b.data = v;\n"
                       "  endtask\n"
                       "endmodule\n"
                       "module cli(bus.client b);\n"
                       "  initial begin\n"
                       "    b.send(8'd23);\n"
                       "    $display(\"%0d at %0t\", b.data, $time);\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  bus b();\n"
                       "  prov p(b.provider);\n"
                       "  cli c(b.client);\n"
                       "endmodule\n"),
      "23 at 2\n");
}

TEST(InterfaceOverviewSim, AForkjoinTaskRunsInEveryModuleDefiningItAtOnce) {
  EXPECT_EQ(RunWithoutErrors("interface bus;\n"
                             "  extern forkjoin task ping(input int n);\n"
                             "  modport tgt(export task ping(input int n));\n"
                             "endinterface\n"
                             "module tgt1(bus.tgt b);\n"
                             "  task b.ping(input int n);\n"
                             "    #3 $display(\"t1 %0d at %0t\", n, $time);\n"
                             "  endtask\n"
                             "endmodule\n"
                             "module tgt2(bus.tgt b);\n"
                             "  task b.ping(input int n);\n"
                             "    #5 $display(\"t2 %0d at %0t\", n, $time);\n"
                             "  endtask\n"
                             "endmodule\n"
                             "module top;\n"
                             "  bus b();\n"
                             "  tgt1 a(b.tgt);\n"
                             "  tgt2 c(b.tgt);\n"
                             "  initial begin\n"
                             "    b.ping(7);\n"
                             "    $display(\"all done at %0t\", $time);\n"
                             "  end\n"
                             "endmodule\n"),
            "t1 7 at 3\nt2 7 at 5\nall done at 5\n");
}

}  // namespace
