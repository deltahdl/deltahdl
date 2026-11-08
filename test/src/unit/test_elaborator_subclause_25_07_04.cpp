#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kMultiExportInterface =
    "interface simple_bus (input logic clk);\n"
    "  logic req, gnt;\n"
    "  logic [7:0] addr, data;\n"
    "  extern forkjoin task countTargets();\n"
    "  extern forkjoin task Read (input logic [7:0] raddr);\n"
    "  extern forkjoin task Write(input logic [7:0] waddr);\n"
    "\n"
    "  modport target(input req, addr, clk,\n"
    "                 output gnt,\n"
    "                 ref data,\n"
    "                 export Read, Write, countTargets);\n"
    "\n"
    "  modport initiator(input gnt, clk,\n"
    "                    output req, addr,\n"
    "                    ref data,\n"
    "                    import task Read (input logic [7:0] raddr),\n"
    "                           task Write(input logic [7:0] waddr));\n"
    "endinterface\n";

TEST(MultipleTaskExports,
     TwoInstancesOfSameModportTypeWithExternForkjoinTaskElaborate) {
  std::string src = kMultiExportInterface;
  src +=
      "module memMod(interface a);\n"
      "  task a.Read(input logic [7:0] raddr);\n"
      "  endtask\n"
      "  task a.Write(input logic [7:0] waddr);\n"
      "  endtask\n"
      "  task a.countTargets();\n"
      "  endtask\n"
      "endmodule\n"
      "module cpuMod(interface b);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  memMod mem1(sb_intf.target);\n"
      "  memMod mem2(sb_intf.target);\n"
      "  cpuMod cpu(sb_intf.initiator);\n"
      "endmodule\n";
  EXPECT_TRUE(ElabOk(src));
}

TEST(MultipleTaskExports,
     ExternForkjoinTaskExportedViaFullPrototypeModportElaborates) {
  EXPECT_TRUE(
      ElabOk("interface simple_bus (input logic clk);\n"
             "  extern forkjoin task Read(input logic [7:0] raddr);\n"
             "  modport target(input clk,\n"
             "                 export task Read(input logic [7:0] raddr));\n"
             "endinterface\n"
             "module memMod(interface a);\n"
             "  task a.Read(input logic [7:0] raddr);\n"
             "  endtask\n"
             "endmodule\n"
             "module top;\n"
             "  logic clk = 0;\n"
             "  simple_bus sb_intf(clk);\n"
             "  memMod mem1(sb_intf.target);\n"
             "  memMod mem2(sb_intf.target);\n"
             "endmodule\n"));
}

TEST(MultipleTaskExports, DuplicateNonForkjoinTaskExportFromTwoModulesIsError) {
  ElabFixture f;
  ElabOk(
      "interface simple_bus (input logic clk);\n"
      "  extern task Read(input logic [7:0] raddr);\n"
      "  modport target(input clk,\n"
      "                 export Read);\n"
      "endinterface\n"
      "module memMod(interface a);\n"
      "  task a.Read(input logic [7:0] raddr);\n"
      "  endtask\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  memMod mem1(sb_intf.target);\n"
      "  memMod mem2(sb_intf.target);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 'Read' exported by more than one module "
                            "connected to interface instance 'sb_intf'",
                            7, "25.7.4"));
}

TEST(MultipleTaskExports, DifferentModuleTypesDuplicateTaskExportIsError) {
  ElabFixture f;
  ElabOk(
      "interface simple_bus (input logic clk);\n"
      "  extern task Read(input logic [7:0] raddr);\n"
      "  modport target(input clk,\n"
      "                 export Read);\n"
      "endinterface\n"
      "module memMod(interface a);\n"
      "  task a.Read(input logic [7:0] raddr);\n"
      "  endtask\n"
      "endmodule\n"
      "module altMod(interface a);\n"
      "  task a.Read(input logic [7:0] raddr);\n"
      "  endtask\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  memMod mem(sb_intf.target);\n"
      "  altMod alt(sb_intf.target);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 'Read' exported by more than one module "
                            "connected to interface instance 'sb_intf'",
                            7, "25.7.4"));
}

TEST(MultipleTaskExports, SingleModuleExportOfTaskWithoutForkjoinElaborates) {
  EXPECT_TRUE(
      ElabOk("interface simple_bus (input logic clk);\n"
             "  extern task Read(input logic [7:0] raddr);\n"
             "  modport target(input clk,\n"
             "                 export Read);\n"
             "endinterface\n"
             "module memMod(interface a);\n"
             "  task a.Read(input logic [7:0] raddr);\n"
             "  endtask\n"
             "endmodule\n"
             "module top;\n"
             "  logic clk = 0;\n"
             "  simple_bus sb_intf(clk);\n"
             "  memMod mem(sb_intf.target);\n"
             "endmodule\n"));
}

TEST(MultipleTaskExports, DuplicateFunctionExportFromTwoModulesIsError) {
  ElabFixture f;
  ElabOk(
      "interface simple_bus (input logic clk);\n"
      "  extern function int compute(input int a);\n"
      "  modport target(input clk,\n"
      "                 export compute);\n"
      "endinterface\n"
      "module memMod(interface a);\n"
      "  function int a.compute(input int x);\n"
      "    return x;\n"
      "  endfunction\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  memMod mem1(sb_intf.target);\n"
      "  memMod mem2(sb_intf.target);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'compute' exported by more than one "
                            "module connected to interface instance 'sb_intf'",
                            7, "25.7.4"));
}

TEST(MultipleTaskExports, SingleModuleExportOfFunctionElaborates) {
  EXPECT_TRUE(
      ElabOk("interface simple_bus (input logic clk);\n"
             "  extern function int compute(input int a);\n"
             "  modport target(input clk,\n"
             "                 export compute);\n"
             "endinterface\n"
             "module memMod(interface a);\n"
             "  function int a.compute(input int x);\n"
             "    return x;\n"
             "  endfunction\n"
             "endmodule\n"
             "module top;\n"
             "  logic clk = 0;\n"
             "  simple_bus sb_intf(clk);\n"
             "  memMod mem(sb_intf.target);\n"
             "endmodule\n"));
}

TEST(MultipleTaskExports, DifferentModuleTypesDuplicateFunctionExportIsError) {
  ElabFixture f;
  ElabOk(
      "interface simple_bus (input logic clk);\n"
      "  extern function int compute(input int a);\n"
      "  modport target(input clk,\n"
      "                 export compute);\n"
      "endinterface\n"
      "module memMod(interface a);\n"
      "  function int a.compute(input int x);\n"
      "    return x;\n"
      "  endfunction\n"
      "endmodule\n"
      "module altMod(interface a);\n"
      "  function int a.compute(input int x);\n"
      "    return x;\n"
      "  endfunction\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  memMod mem(sb_intf.target);\n"
      "  altMod alt(sb_intf.target);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'compute' exported by more than one "
                            "module connected to interface instance 'sb_intf'",
                            7, "25.7.4"));
}

TEST(MultipleTaskExports,
     ExternForkjoinTaskWithoutAnyDefiningModuleElaborates) {
  EXPECT_TRUE(
      ElabOk("interface simple_bus (input logic clk);\n"
             "  extern forkjoin task countTargets();\n"
             "  modport initiator(input clk);\n"
             "endinterface\n"
             "module cpuMod(interface b);\n"
             "endmodule\n"
             "module top;\n"
             "  logic clk = 0;\n"
             "  simple_bus sb_intf(clk);\n"
             "  cpuMod cpu(sb_intf.initiator);\n"
             "endmodule\n"));
}

}  // namespace
