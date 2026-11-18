#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string RunWithoutErrors(const std::string& src) {
  SimFixture f;
  auto out = RunCapture(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  return out;
}

TEST(InterfacePortsSim, TwoInstancesShareOneExternalWire) {
  EXPECT_EQ(
      RunWithoutErrors("interface simple_bus(input logic clk);\n"
                       "  logic req, gnt;\n"
                       "endinterface\n"
                       "module memMod(simple_bus a);\n"
                       "  int n = 0;\n"
                       "  always @(posedge a.clk) n++;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic clk = 0;\n"
                       "  simple_bus sb_intf1(clk);\n"
                       "  simple_bus sb_intf2(clk);\n"
                       "  memMod mem1(.a(sb_intf1));\n"
                       "  memMod mem2(.a(sb_intf2));\n"
                       "  initial begin\n"
                       "    #1 clk = 1; #1 clk = 0; #1 clk = 1;\n"
                       "    #1 $display(\"%0d %0d %b %b\", mem1.n, mem2.n,\n"
                       "                sb_intf1.clk, sb_intf2.clk);\n"
                       "  end\n"
                       "endmodule\n"),
      "2 2 1 1\n");
}

TEST(InterfacePortsSim, AnOutputPortDrivesTheExternalNet) {
  EXPECT_EQ(RunWithoutErrors("interface I(input logic a, output logic b);\n"
                             "  assign b = ~a;\n"
                             "endinterface\n"
                             "module reader(I p);\n"
                             "  initial #2 $display(\"port %b\", p.b);\n"
                             "endmodule\n"
                             "module top;\n"
                             "  logic x = 0;\n"
                             "  wire y;\n"
                             "  I i(x, y);\n"
                             "  reader r(i);\n"
                             "  initial begin\n"
                             "    #1 $display(\"y %b\", y);\n"
                             "    x = 1;\n"
                             "    #2 $display(\"y %b\", y);\n"
                             "  end\n"
                             "endmodule\n"),
            "y 1\nport 0\ny 0\n");
}

TEST(InterfacePortsSim, AnInoutPortResolvesDriversInsideAndOutside) {
  EXPECT_EQ(RunWithoutErrors("interface I(inout wire w);\n"
                             "  logic in_v = 1'bz;\n"
                             "  assign w = in_v;\n"
                             "endinterface\n"
                             "module top;\n"
                             "  logic out_v = 1'bz;\n"
                             "  wire n;\n"
                             "  assign n = out_v;\n"
                             "  I i(n);\n"
                             "  initial begin\n"
                             "    #1 i.in_v = 0;\n"
                             "    #1 $display(\"%b %b\", n, i.w);\n"
                             "    out_v = 1;\n"
                             "    #1 $display(\"%b %b\", n, i.w);\n"
                             "    i.in_v = 1'bz;\n"
                             "    #1 $display(\"%b %b\", n, i.w);\n"
                             "  end\n"
                             "endmodule\n"),
            "0 0\nx x\n1 1\n");
}

TEST(InterfacePortsSim, AnInterfacesPortOfAnInterfaceTypeDenotesTheActual) {
  for (const char* form : {"interface outer(simple_bus b);|outer o(.b(sb));",
                           "interface outer(simple_bus b);|outer o(sb);",
                           "interface outer(simple_bus.mp b);|outer o(.b(sb));",
                           "interface outer(interface b);|outer o(.b(sb));"}) {
    std::string f(form);
    auto bar = f.find('|');
    EXPECT_EQ(RunWithoutErrors("interface simple_bus;\n"
                               "  logic [7:0] req, gnt;\n"
                               "  modport mp(output req, input gnt);\n"
                               "endinterface\n" +
                               f.substr(0, bar) +
                               "\n"
                               "  initial #1 b.req = 8'd4;\n"
                               "  initial #3 $display(\"outer sees %0d\", "
                               "b.gnt);\n"
                               "endinterface\n"
                               "module top;\n"
                               "  simple_bus sb();\n"
                               "  " +
                               f.substr(bar + 1) +
                               "\n"
                               "  initial #2 begin\n"
                               "    $display(\"top sees %0d\", sb.req);\n"
                               "    sb.gnt = 8'd9;\n"
                               "  end\n"
                               "endmodule\n"),
              "top sees 4\nouter sees 9\n")
        << form;
  }
}

TEST(InterfacePortsSim, ASurplusPositionalActualLeavesTheBodyMemberAlone) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface simple_bus(input logic clk);\n"
                       "  logic req;\n"
                       "endinterface\n"
                       "module top;\n"
                       "  logic c = 1, d = 1;\n"
                       "  simple_bus sb(c, d);\n"
                       "  initial #1 $display(\"%b %b\", sb.clk, sb.req);\n"
                       "endmodule\n",
                       f),
            "1 x\n");
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), "too many ordered port", 6,
                              "23.3.2.1"));
}

TEST(InterfacePortsSim, AWildcardConnectionLeavesTheBodyMemberAlone) {
  EXPECT_EQ(
      RunWithoutErrors("interface simple_bus(input logic clk);\n"
                       "  logic req;\n"
                       "endinterface\n"
                       "module top;\n"
                       "  logic clk = 1, req = 1;\n"
                       "  simple_bus sb(.*);\n"
                       "  initial #1 $display(\"%b %b\", sb.clk, sb.req);\n"
                       "endmodule\n"),
      "1 x\n");
}

}  // namespace
