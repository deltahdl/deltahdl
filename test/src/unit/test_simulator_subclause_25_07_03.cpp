#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(InterfaceExportSim, ExportedTaskRunsInTheDefiningModule) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface simple_bus;\n"
                       "  logic [7:0] addr;\n"
                       "  modport target(ref addr, export Read);\n"
                       "  modport initiator(ref addr, import task "
                       "Read(input logic [7:0] raddr));\n"
                       "endinterface\n"
                       "module memMod(simple_bus.target a);\n"
                       "  logic avail = 1;\n"
                       "  task a.Read(input logic [7:0] raddr);\n"
                       "    avail = 0;\n"
                       "    #4 $display(\"Read raddr=%0d avail=%0d\", raddr, "
                       "avail);\n"
                       "    avail = 1;\n"
                       "  endtask\n"
                       "endmodule\n"
                       "module cpuMod(simple_bus.initiator b);\n"
                       "  initial begin\n"
                       "    b.Read(17);\n"
                       "    $display(\"after avail=%0d t=%0t\", "
                       "top.mem.avail, $time);\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  simple_bus sb_intf();\n"
                       "  memMod mem(sb_intf.target);\n"
                       "  cpuMod cpu(sb_intf.initiator);\n"
                       "endmodule\n",
                       f),
            "Read raddr=17 avail=0\nafter avail=1 t=4\n");
}

}  // namespace
