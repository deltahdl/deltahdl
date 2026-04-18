#include "fixture_elaborator.h"

using namespace delta;

namespace {

constexpr const char* kSimpleBusInterface =
    "interface simple_bus (input logic clk);\n"
    "  logic req, gnt;\n"
    "  logic [7:0] addr, data;\n"
    "  logic [1:0] mode;\n"
    "  logic start, rdy;\n"
    "\n"
    "  modport target (input req, addr, mode, start, clk,\n"
    "                  output gnt, rdy,\n"
    "                  ref data,\n"
    "                  import targetRead,\n"
    "                         targetWrite);\n"
    "\n"
    "  modport initiator(input gnt, rdy, clk,\n"
    "                    output req, addr, mode, start,\n"
    "                    ref data,\n"
    "                    import initiatorRead,\n"
    "                           initiatorWrite);\n"
    "\n"
    "  task initiatorRead(input logic [7:0] raddr);\n"
    "  endtask\n"
    "  task targetRead;\n"
    "  endtask\n"
    "  task initiatorWrite(input logic [7:0] waddr);\n"
    "  endtask\n"
    "  task targetWrite;\n"
    "  endtask\n"
    "endinterface\n";

TEST(ReadWriteInterfaceExample, ElaboratesFullExampleTopology) {
  std::string src = kSimpleBusInterface;
  src +=
      "module memMod(interface a);\n"
      "endmodule\n"
      "module cpuMod(interface b);\n"
      "endmodule\n"
      "module omniMod(interface b);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  memMod mem(sb_intf.target);\n"
      "  cpuMod cpu(sb_intf.initiator);\n"
      "  omniMod omni(sb_intf);\n"
      "endmodule\n";
  EXPECT_TRUE(ElabOk(src));
}

TEST(ReadWriteInterfaceExample, ModportSelectorAndBareInterfaceBindingsCoexist) {
  std::string src = kSimpleBusInterface;
  src +=
      "module restricted(interface a);\n"
      "endmodule\n"
      "module unrestricted(interface a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  restricted r(sb_intf.target);\n"
      "  unrestricted u(sb_intf);\n"
      "endmodule\n";
  EXPECT_TRUE(ElabOk(src));
}

TEST(ReadWriteInterfaceExample, BothModportsBindInTheSameTopology) {
  std::string src = kSimpleBusInterface;
  src +=
      "module side_a(interface a);\n"
      "endmodule\n"
      "module side_b(interface b);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  side_a a_inst(sb_intf.target);\n"
      "  side_b b_inst(sb_intf.initiator);\n"
      "endmodule\n";
  EXPECT_TRUE(ElabOk(src));
}

}  // namespace
