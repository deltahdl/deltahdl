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

// §25.7.4 accepts the forkjoin exemption regardless of how the modport names
// the exported task. Here the modport uses the full-prototype export form
// (`export task Read(...)`) rather than the bare identifier, exercising the
// dependency (§25.5/§25.7) prototype syntax the duplicate-export check
// consumes.
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
  // The report stands at the first of the two exporting definitions, which for
  // two instances of one module is memMod's single body on line 7.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 'Read' exported by more than one module "
                            "connected to interface instance 'sb_intf'",
                            7, "25.7.4"));
}

// §25.7.4's general rule is stated over "more than one module" — not only
// repeated instances of one module type. Two DISTINCT module types exporting
// the same non-forkjoin task into one interface instance is likewise an error.
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
  // The export sites are collected in instantiation order, so the first is
  // memMod's body on line 7 rather than altMod's on line 11.
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

// Positive control witnessing that the duplicate-function negative above fires
// on the second export, not on function export being unsupported: a single
// module exporting the function elaborates.
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

// The no-forkjoin-escape for functions also holds across distinct module
// types: two different modules exporting the same function is an error.
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
  // memMod is instantiated first, so its definition on line 7 is the site the
  // report stands at.
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
