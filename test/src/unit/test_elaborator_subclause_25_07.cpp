#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(InterfaceSubroutines, InterfaceWithSubroutinesElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc;\n"
      "  function automatic int xform(int v); return v; endfunction\n"
      "  task send; endtask\n"
      "endinterface\n",
      f, "ifc");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ModportDeclarationElaboration, ImportExportModportElaborates) {
  EXPECT_TRUE(
      ElabOk("interface ifc;\n"
             "  task Read; endtask\n"
             "  modport mp(import Read, export Write);\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ModportDeclarationElaboration, ImportPrototypeElaborates) {
  EXPECT_TRUE(
      ElabOk("interface ifc;\n"
             "  modport mp(\n"
             "    import function int compute(int a),\n"
             "    import task do_work(int x)\n"
             "  );\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceSubroutines, ExternPrototypeWithoutBodyElaborates) {
  EXPECT_TRUE(
      ElabOk("interface ifc;\n"
             "  extern function int compute(input int a);\n"
             "  extern task run(input int x);\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceSubroutines, ExternForkjoinTaskPrototypeElaborates) {
  EXPECT_TRUE(
      ElabOk("interface ifc;\n"
             "  extern forkjoin task parallel_run(input int id);\n"
             "endinterface\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceSubroutines, HierarchicalTaskBodyElaborates) {
  EXPECT_TRUE(
      ElabOk("interface ifc;\n"
             "  extern task my_task(input int x);\n"
             "endinterface\n"
             "task ifc.my_task(input int x);\n"
             "endtask\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceSubroutines, HierarchicalTaskBodyWithoutExternPrototypeIsError) {
  ElabFixture f;
  ElabOk(
      "interface ifc;\n"
      "endinterface\n"
      "task ifc.my_task(input int x);\n"
      "endtask\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "no matching extern prototype for 'ifc.my_task' in "
                            "interface 'ifc'",
                            3, "25.7"));
}

TEST(InterfaceSubroutines, HierarchicalBodyArgumentCountMismatchIsError) {
  ElabFixture f;
  ElabOk(
      "interface ifc;\n"
      "  extern task my_task(input int x);\n"
      "endinterface\n"
      "task ifc.my_task(input int x, input int y);\n"
      "endtask\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "out-of-block declaration for 'ifc.my_task' has 2 "
                            "argument(s) but the prototype has 1",
                            4, "25.7"));
}

TEST(InterfaceSubroutines, HierarchicalBodyArgumentTypeMismatchIsError) {
  ElabFixture f;
  ElabOk(
      "interface ifc;\n"
      "  extern task my_task(input int x);\n"
      "endinterface\n"
      "task ifc.my_task(input bit x);\n"
      "endtask\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "out-of-block declaration for 'ifc.my_task' "
                            "argument 'x' has mismatched type",
                            4, "25.7"));
}

TEST(InterfaceSubroutines, HierarchicalBodyArgumentDirectionMismatchIsError) {
  ElabFixture f;
  ElabOk(
      "interface ifc;\n"
      "  extern task my_task(input int x);\n"
      "endinterface\n"
      "task ifc.my_task(output int x);\n"
      "endtask\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "out-of-block declaration for 'ifc.my_task' "
                            "argument 'x' has mismatched direction",
                            4, "25.7"));
}

TEST(InterfaceSubroutines, HierarchicalFunctionBodyReturnTypeMismatchIsError) {
  ElabFixture f;
  ElabOk(
      "interface ifc;\n"
      "  extern function int my_func(input int a);\n"
      "endinterface\n"
      "function bit ifc.my_func(input int a);\n"
      "  return 0;\n"
      "endfunction\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "out-of-block declaration for 'ifc.my_func' has "
                            "mismatched return type",
                            4, "25.7"));
}

TEST(InterfaceSubroutines, HierarchicalBodyKindMismatchIsError) {
  ElabFixture f;
  ElabOk(
      "interface ifc;\n"
      "  extern task my_task(input int x);\n"
      "endinterface\n"
      "function int ifc.my_task(input int x);\n"
      "  return x;\n"
      "endfunction\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "out-of-block declaration for 'ifc.my_task' is a "
                            "function but the prototype is a task",
                            4, "25.7"));
}

TEST(ModportDeclarationElaboration,
     ExportPrototypeMatchingDefinitionElaborates) {
  EXPECT_TRUE(
      ElabOk("interface simple_bus(input logic clk);\n"
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
             "  memMod mem(sb_intf.target);\n"
             "endmodule\n"));
}

TEST(ModportDeclarationElaboration,
     ExportPrototypeMismatchedDefinitionIsError) {
  ElabFixture f;
  ElabOk(
      "interface simple_bus(input logic clk);\n"
      "  modport target(input clk,\n"
      "                 export task Read(input logic [7:0] raddr));\n"
      "endinterface\n"
      "module memMod(interface a);\n"
      "  task a.Read(input logic [3:0] raddr);\n"
      "  endtask\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  memMod mem(sb_intf.target);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "definition of exported subroutine 'Read' in "
                            "module 'memMod' does not match the prototype "
                            "declared in the modport",
                            6, "25.7"));
}

TEST(ModportDeclarationElaboration,
     ExportFunctionPrototypeMatchingReturnElaborates) {
  EXPECT_TRUE(
      ElabOk("interface simple_bus(input logic clk);\n"
             "  modport target(input clk,\n"
             "                 export function int compute(input int a));\n"
             "endinterface\n"
             "module memMod(interface a);\n"
             "  function int a.compute(input int a_arg);\n"
             "    return a_arg;\n"
             "  endfunction\n"
             "endmodule\n"
             "module top;\n"
             "  logic clk = 0;\n"
             "  simple_bus sb_intf(clk);\n"
             "  memMod mem(sb_intf.target);\n"
             "endmodule\n"));
}

TEST(ModportDeclarationElaboration,
     ExportFunctionPrototypeReturnMismatchIsError) {
  ElabFixture f;
  ElabOk(
      "interface simple_bus(input logic clk);\n"
      "  modport target(input clk,\n"
      "                 export function int compute(input int a));\n"
      "endinterface\n"
      "module memMod(interface a);\n"
      "  function bit a.compute(input int a_arg);\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  memMod mem(sb_intf.target);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "definition of exported subroutine 'compute' in "
                            "module 'memMod' does not match the prototype "
                            "declared in the modport",
                            6, "25.7"));
}

TEST(ModportDeclarationElaboration,
     ExportPrototypeUndefinedInConnectedModuleIsError) {
  ElabFixture f;
  ElabOk(
      "interface simple_bus(input logic clk);\n"
      "  modport target(input clk,\n"
      "                 export task Read(input logic [7:0] raddr));\n"
      "endinterface\n"
      "module memMod(interface a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  memMod mem(sb_intf.target);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'memMod' is connected to modport 'target' "
                            "of interface instance 'sb_intf', which exports "
                            "subroutine 'Read', but the module does not define "
                            "it",
                            3, "25.7"));
}

TEST(ModportDeclarationElaboration,
     ExportBareIdentifierUndefinedInConnectedModuleIsError) {
  ElabFixture f;
  ElabOk(
      "interface simple_bus(input logic clk);\n"
      "  modport target(input clk, export Read);\n"
      "endinterface\n"
      "module memMod(interface a);\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  memMod mem(sb_intf.target);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'memMod' is connected to modport 'target' "
                            "of interface instance 'sb_intf', which exports "
                            "subroutine 'Read', but the module does not define "
                            "it",
                            2, "25.7"));
}

TEST(ModportDeclarationElaboration,
     ExportBareIdentifierDefinedInConnectedModuleElaborates) {
  EXPECT_TRUE(
      ElabOk("interface simple_bus(input logic clk);\n"
             "  modport target(input clk, export Read);\n"
             "endinterface\n"
             "module memMod(interface a);\n"
             "  task a.Read;\n"
             "  endtask\n"
             "endmodule\n"
             "module top;\n"
             "  logic clk = 0;\n"
             "  simple_bus sb_intf(clk);\n"
             "  memMod mem(sb_intf.target);\n"
             "endmodule\n"));
}

TEST(ModportDeclarationElaboration,
     ExportPrototypeArgumentCountMismatchIsError) {
  ElabFixture f;
  ElabOk(
      "interface simple_bus(input logic clk);\n"
      "  modport target(input clk,\n"
      "                 export task Read(input logic [7:0] raddr));\n"
      "endinterface\n"
      "module memMod(interface a);\n"
      "  task a.Read(input logic [7:0] raddr, input int extra);\n"
      "  endtask\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  memMod mem(sb_intf.target);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "definition of exported subroutine 'Read' in "
                            "module 'memMod' does not match the prototype "
                            "declared in the modport",
                            6, "25.7"));
}

TEST(ModportDeclarationElaboration,
     ExportPrototypeArgumentDirectionMismatchIsError) {
  ElabFixture f;
  ElabOk(
      "interface simple_bus(input logic clk);\n"
      "  modport target(input clk,\n"
      "                 export task Read(input logic [7:0] raddr));\n"
      "endinterface\n"
      "module memMod(interface a);\n"
      "  task a.Read(output logic [7:0] raddr);\n"
      "  endtask\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  memMod mem(sb_intf.target);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "definition of exported subroutine 'Read' in "
                            "module 'memMod' does not match the prototype "
                            "declared in the modport",
                            6, "25.7"));
}

TEST(ModportDeclarationElaboration, ExportPrototypeKindMismatchIsError) {
  ElabFixture f;
  ElabOk(
      "interface simple_bus(input logic clk);\n"
      "  modport target(input clk,\n"
      "                 export task Read(input logic [7:0] raddr));\n"
      "endinterface\n"
      "module memMod(interface a);\n"
      "  function int a.Read(input logic [7:0] raddr);\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  memMod mem(sb_intf.target);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "definition of exported subroutine 'Read' in "
                            "module 'memMod' does not match the prototype "
                            "declared in the modport",
                            6, "25.7"));
}

TEST(InterfaceSubroutines, HierarchicalFunctionBodyElaborates) {
  EXPECT_TRUE(
      ElabOk("interface ifc;\n"
             "  extern function int my_func(input int a);\n"
             "endinterface\n"
             "function int ifc.my_func(input int a);\n"
             "  return a;\n"
             "endfunction\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ModportDeclarationElaboration,
     HierarchicalModuleBodyNotAnnouncedByInterfaceIsError) {
  ElabFixture f;
  ElabOk(
      "interface simple_bus(input logic clk);\n"
      "  modport target(input clk);\n"
      "endinterface\n"
      "module memMod(interface a);\n"
      "  task a.Read(input logic [7:0] raddr);\n"
      "  endtask\n"
      "endmodule\n"
      "module top;\n"
      "  logic clk = 0;\n"
      "  simple_bus sb_intf(clk);\n"
      "  memMod mem(sb_intf.target);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "subroutine 'Read' defined in module 'memMod' for "
                            "interface port 'a' by a hierarchical name is "
                            "neither declared 'extern' in interface "
                            "'simple_bus' nor exported by any of its modports",
                            5, "25.7"));
}

TEST(ModportDeclarationElaboration,
     HierarchicalModuleBodyAnnouncedByExternElaborates) {
  EXPECT_TRUE(
      ElabOk("interface simple_bus(input logic clk);\n"
             "  extern task Read(input logic [7:0] raddr);\n"
             "  modport target(input clk);\n"
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

TEST(ModportImportPrototype, MismatchWithTheDeclarationIsRefused) {
  ElabFixture f;
  ElaborateSrc(
      "interface sb;\n"
      "  function automatic int f(int a); return a; endfunction\n"
      "  function automatic int g(int a, int b = 9); return b; endfunction\n"
      "  modport mp(import function int f(int a, int b));\n"
      "  modport mq(import function int g(int a, int z = 9));\n"
      "endinterface\n",
      f, "sb");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the prototype of 'f' modport 'mp' imports does "
                            "not match its declaration in interface 'sb'",
                            4, "25.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the prototype of 'g' modport 'mq' imports does "
                            "not match its declaration in interface 'sb'",
                            5, "25.7"));
}

TEST(ModportImportPrototype, MatchingPrototypesAreAccepted) {
  EXPECT_TRUE(
      ElabOk("interface sb;\n"
             "  extern task Read(input logic [7:0] raddr);\n"
             "  function automatic int f(int a, int b); return b; endfunction\n"
             "  modport mp(import function int f(int a, int b));\n"
             "  modport mq(import function int f(int, int));\n"
             "  modport mr(import task Read(input logic [7:0] raddr));\n"
             "endinterface\n"
             "module m; endmodule\n"));
}

TEST(ModportImportPrototype, IdentifierImportFromAnotherModuleIsRefused) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus (input logic clk);\n"
      "  extern task Read(input logic [7:0] raddr);\n"
      "  modport target(input clk, export Read);\n"
      "  modport initiator(input clk, import Read);\n"
      "endinterface\n"
      "module memMod(interface a);\n"
      "  task a.Read(input logic [7:0] raddr); endtask\n"
      "endmodule\n"
      "module cpuMod(simple_bus.initiator b); initial #1 b.Read(7); endmodule\n"
      "module top; logic clk = 0; simple_bus sb_intf(clk);\n"
      "  memMod mem(sb_intf.target); cpuMod cpu(sb_intf.initiator);\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "modport 'initiator' imports 'Read', which "
                            "interface 'simple_bus' does not define, by its "
                            "name alone; importing a subroutine another "
                            "module defines needs a full prototype",
                            4, "25.7"));
}

TEST(ModportImportPrototype, IdentifierImportCallsNeedingAPrototypeAreRefused) {
  ElabFixture f;
  ElaborateSrc(
      "interface sb;\n"
      "  function automatic int f(int a = 5, int b = 6); return a; "
      "endfunction\n"
      "  modport mp(import f);\n"
      "endinterface\n"
      "module m(sb.mp p);\n"
      "  initial $display(\"%0d\", p.f(.a(3)));\n"
      "  initial $display(\"%0d\", p.f());\n"
      "  initial $display(\"%0d\", p.f(, 2));\n"
      "  initial $display(\"%0d\", p.f(1, 2));\n"
      "endmodule\n"
      "module top; sb s(); m u(s.mp); endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the call of 'f' through modport 'mp' binds an "
                            "argument by name, which needs a full prototype "
                            "of 'f' in the modport",
                            6, "25.7"));
  for (int line : {7, 8}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "the call of 'f' through modport 'mp' relies on "
                              "a default argument value, which needs a full "
                              "prototype of 'f' in the modport",
                              line, "25.7"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "the call of 'f' through modport 'mp' relies on "
                             "a default argument value, which needs a full "
                             "prototype of 'f' in the modport",
                             9, "25.7"));
}

TEST(ModportImportPrototype, ArgumentThePrototypeGivesNoDefaultIsRefused) {
  ElabFixture f;
  ElaborateSrc(
      "interface sb;\n"
      "  function automatic int f(int a, int b = 9); return b; endfunction\n"
      "  modport mp(import function int f(int a, int b));\n"
      "endinterface\n"
      "module m(sb.mp p); initial $display(\"v=%0d\", p.f(1)); endmodule\n"
      "module top; sb s(); m u(s.mp); endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the call of 'f' through modport 'mp' omits "
                            "argument 'b', which the modport's prototype "
                            "gives no default",
                            5, "25.7"));
}

TEST(ModportImportPrototype, OtherCallsAreNoImportCalls) {
  ElabFixture f;
  ElaborateSrc(
      "interface sb;\n"
      "  function automatic int f(int a); return a; endfunction\n"
      "  function automatic int g(); return 3; endfunction\n"
      "  modport mp(import f);\n"
      "endinterface\n"
      "class C; function int h(); return 4; endfunction endclass\n"
      "module m(sb.mp p);\n"
      "  C c;\n"
      "  initial begin c = new; $display(\"%0d %0d\", c.h(), p.g()); end\n"
      "endmodule\n"
      "module top; sb s(); m u(s.mp); endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'g' is not accessible through modport 'mp' of "
                            "interface 'sb'",
                            9, "25.5"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

}  // namespace
