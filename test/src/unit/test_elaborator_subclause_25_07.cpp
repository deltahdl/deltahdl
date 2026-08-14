

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

// §25.7: a subroutine defined for an interface using a hierarchical name shall
// also be declared as extern in that interface. A hierarchical body with no
// matching extern prototype is an elaboration error.
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

// §25.7: the number of arguments in a prototype shall match the number in the
// subroutine declaration. The hierarchical body here supplies an extra formal.
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
  // The signature comparison an interface's hierarchical body goes through is
  // the one ValidateOutOfBlockSignature runs for a class out-of-block body, so
  // the report names §8.24 rather than the §25.7 rule this case is about.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "out-of-block declaration for 'ifc::my_task' has 2 "
                            "argument(s) but the prototype has 1",
                            4, "8.24"));
}

// §25.7: the types of the arguments in a prototype shall match those in the
// subroutine declaration. Here the body widens the argument type.
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
  // §8.24 for the reason given in HierarchicalBodyArgumentCountMismatchIsError.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "out-of-block declaration for 'ifc::my_task' "
                            "argument 'x' has mismatched type",
                            4, "8.24"));
}

// §25.7: argument directions named by a prototype shall match the subroutine
// declaration. Here the body flips the direction from input to output.
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
  // §8.24 for the reason given in HierarchicalBodyArgumentCountMismatchIsError.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "out-of-block declaration for 'ifc::my_task' "
                            "argument 'x' has mismatched direction",
                            4, "8.24"));
}

// §25.7: a function prototype specifies the return value as well as the
// arguments, so the hierarchical body's return type shall match the prototype.
// Here the prototype returns int but the body returns bit.
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
  // §8.24 for the reason given in HierarchicalBodyArgumentCountMismatchIsError.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "out-of-block declaration for 'ifc::my_func' has "
                            "mismatched return type",
                            4, "8.24"));
}

// §25.7: a prototype is either a function prototype or a task prototype, so the
// hierarchical body shall agree in kind with its prototype. Here the interface
// declares an extern task but the body is written as a function.
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
  // §8.24 for the reason given in HierarchicalBodyArgumentCountMismatchIsError.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "out-of-block declaration for 'ifc::my_task' is a "
                            "function but the prototype is a task",
                            4, "8.24"));
}

// §25.7: when a modport exports a subroutine via a full prototype, a connected
// module that supplies a matching definition elaborates without error.
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

// §25.7: a module's definition of an exported subroutine must match the
// modport's exported prototype exactly; here the argument width differs, which
// is an elaboration error.
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
  // One report covers every way a definition can fail to match an exported
  // prototype, so the message names the subroutine and the defining module
  // rather than the part of the signature that differs; the line is the
  // definition's.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "definition of exported subroutine 'Read' in "
                            "module 'memMod' does not match the prototype "
                            "declared in the modport",
                            6, "25.7"));
}

// §25.7: matching includes the return value for an exported function prototype;
// a definition whose return type agrees elaborates cleanly.
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

// §25.7: an exported function whose definition returns a different type than
// the modport prototype does not match, which is an elaboration error.
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

// §25.7: if a module is connected to a modport that contains an exported
// subroutine and the module does not define that subroutine, an elaboration
// error shall occur. Here memMod binds the exporting `target` modport but
// supplies no out-of-block body for the exported task.
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
  // The missing definition is reported where the export was written, which for
  // a full prototype is the `task` keyword on line 3.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'memMod' is connected to modport 'target' "
                            "of interface instance 'sb_intf', which exports "
                            "subroutine 'Read', but the module does not define "
                            "it",
                            3, "25.7"));
}

// §25.7: the same requirement holds when the modport names the exported
// subroutine with a bare identifier rather than a full prototype. The
// connected module must still define it, so its absence is an error.
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
  // A bare identifier export carries no prototype to stand at, so the report
  // stands at the modport declaration on line 2.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'memMod' is connected to modport 'target' "
                            "of interface instance 'sb_intf', which exports "
                            "subroutine 'Read', but the module does not define "
                            "it",
                            2, "25.7"));
}

// §25.7: the missing-definition error is specific to the exported subroutine
// the module was connected to. When the connected module does define the
// exported task with an out-of-block body, elaboration succeeds — this guards
// the negative tests above against reporting an error unconditionally.
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

// §25.7: exact matching of an exported prototype covers the argument count.
// Here the module's definition adds an extra formal beyond the modport
// prototype, which is an elaboration error.
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

// §25.7: exact matching of an exported prototype covers argument directions.
// Here the module flips the argument from input to output, which does not match
// the modport prototype and is an elaboration error.
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

// §25.7: exact matching also fixes the subroutine kind. Here the modport
// exports a task prototype but the module defines a function of the same name,
// so the kinds disagree and elaboration fails.
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

// §25.7: a function defined for an interface by a hierarchical name whose
// signature agrees with the interface's extern function prototype elaborates
// cleanly — the positive function counterpart of the task body accepted above.
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

// §25.7: a subroutine a module supplies for an interface through a hierarchical
// name shall also be announced by the interface — declared extern in it or
// exported by one of its modports. Here memMod defines a.Read for a connected
// interface that neither externs Read nor exports it from any modport, which is
// an elaboration error.
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

// §25.7: the same hierarchical definition is legal once the interface announces
// the subroutine with an extern declaration — the positive control isolating
// the rule above (the only change is adding the extern prototype).
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

}  // namespace
