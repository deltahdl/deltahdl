#include "fixture_elaborator.h"

using namespace delta;

namespace {

constexpr const char* kExportTasksInterface =
    "interface simple_bus (input logic clk);\n"
    "  logic req, gnt;\n"
    "  logic [7:0] addr, data;\n"
    "  logic [1:0] mode;\n"
    "  logic start, rdy;\n"
    "\n"
    "  modport target(input req, addr, mode, start, clk,\n"
    "                 output gnt, rdy,\n"
    "                 ref data,\n"
    "                 export Read,\n"
    "                        Write);\n"
    "\n"
    "  modport initiator(input gnt, rdy, clk,\n"
    "                    output req, addr, mode, start,\n"
    "                    ref data,\n"
    "                    import task Read (input logic [7:0] raddr),\n"
    "                           task Write(input logic [7:0] waddr));\n"
    "endinterface\n";

TEST(ExportTasksExample, InterfaceWithExportAndImportModportsElaborates) {
  std::string src = kExportTasksInterface;
  src += "module m;\nendmodule\n";
  EXPECT_TRUE(ElabOk(src));
}

TEST(ExportTasksExample, ElaboratesModportSelectorTopology) {
  std::string src = kExportTasksInterface;
  src +=
      "module memMod(interface a);\n"
      "endmodule\n"
      "module cpuMod(interface b);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  memMod mem(sb_intf.target);\n"
      "  cpuMod cpu(sb_intf.initiator);\n"
      "endmodule\n";
  EXPECT_TRUE(ElabOk(src));
}

TEST(ExportTasksExample, ElaboratesWithHierarchicalTaskBodiesInExportingModule) {
  std::string src = kExportTasksInterface;
  src +=
      "module memMod(interface a);\n"
      "  logic avail;\n"
      "  task a.Read(input logic [7:0] raddr);\n"
      "    avail = 0;\n"
      "    avail = 1;\n"
      "  endtask\n"
      "  task a.Write(input logic [7:0] waddr);\n"
      "    avail = 0;\n"
      "    avail = 1;\n"
      "  endtask\n"
      "endmodule\n"
      "module cpuMod(interface b);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  memMod mem(sb_intf.target);\n"
      "  cpuMod cpu(sb_intf.initiator);\n"
      "endmodule\n";
  EXPECT_TRUE(ElabOk(src));
}

}  // namespace
