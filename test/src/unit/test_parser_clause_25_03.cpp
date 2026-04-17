#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(InterfaceParsing, EndinterfaceLabel) {
  auto r = Parse(
      "interface simple_bus;\n"
      "endinterface : simple_bus\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces.size(), 1);
  EXPECT_EQ(r.cu->interfaces[0]->name, "simple_bus");
}

TEST(InterfaceParsing, EndinterfaceNoLabel) {
  auto r = Parse(
      "interface my_if;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces.size(), 1);
  EXPECT_EQ(r.cu->interfaces[0]->name, "my_if");
}

TEST(InterfaceParsing, EmptyInterface) {
  auto r = Parse("interface simple_bus; endinterface");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces.size(), 1);
  EXPECT_EQ(r.cu->interfaces[0]->name, "simple_bus");
  EXPECT_EQ(r.cu->interfaces[0]->decl_kind, ModuleDeclKind::kInterface);
}

TEST(InterfaceParsing, ParamsAndPorts) {
  auto r = Parse(
      "interface ifc #(parameter int W = 8)(input logic clk);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->ports.size(), 1u);
}

TEST(InterfaceParsing, MultiplePorts) {
  auto r = Parse(
      "interface bus(input logic clk, input logic rst);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces.size(), 1);
  EXPECT_EQ(r.cu->interfaces[0]->ports.size(), 2);
}

TEST(InterfaceParsing, LifetimeAutomatic) {
  auto r = Parse("interface automatic myif; endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces.size(), 1);
  EXPECT_EQ(r.cu->interfaces[0]->name, "myif");
}

TEST(InterfaceParsing, MissingEndinterfaceIsError) {
  EXPECT_FALSE(ParseOk("interface i;"));
}

TEST(InterfaceParsing, ContainsDeclarations) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic req, gnt;\n"
      "  logic [7:0] data;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->interfaces[0]->items.empty());
}

TEST(InterfaceParsing, InterfaceAndModule) {
  auto r = Parse(
      "interface bus; endinterface\n"
      "module top; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->interfaces.size(), 1);
  EXPECT_EQ(r.cu->modules.size(), 1);
}

TEST(InterfaceParsing, WildcardPorts) {
  auto r = Parse("interface ifc(.*); endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_TRUE(r.cu->interfaces[0]->has_wildcard_ports);
}

TEST(InterfaceParsing, NonAnsiHeader) {
  auto r = Parse(
      "interface ifc(clk);\n"
      "  input clk;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->ports.size(), 1u);
}

TEST(InterfaceParsing, AnsiHeader) {
  auto r = Parse("interface ifc(input logic clk); endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->ports.size(), 1u);
}

TEST(InterfaceParsing, ExternInterface) {
  auto r = Parse("extern interface ifc(input logic clk);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_TRUE(r.cu->interfaces[0]->is_extern);
  EXPECT_EQ(r.cu->interfaces[0]->name, "ifc");
}

TEST(InterfaceItemsParsing, InterfaceMultipleItemTypes) {
  auto r = Parse(
      "interface bus_if;\n"
      "  logic [7:0] data;\n"
      "  extern function void validate();\n"
      "  extern forkjoin task run_parallel();\n"
      "  modport master(output data);\n"
      "  modport slave(input data);\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto* ifc = r.cu->interfaces[0];

  ASSERT_GE(ifc->items.size(), 3u);
  EXPECT_EQ(ifc->modports.size(), 2u);
  EXPECT_TRUE(
      HasItemKindNamed(ifc->items, ModuleItemKind::kFunctionDecl, "validate"));
  EXPECT_TRUE(
      HasItemKindNamed(ifc->items, ModuleItemKind::kTaskDecl, "run_parallel"));
}

TEST(InterfaceItemsParsing, InterfaceContinuousAssign) {
  auto r = Parse(
      "interface ifc;\n"
      "  wire a, b;\n"
      "  assign a = b;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->interfaces[0]->items, ModuleItemKind::kContAssign));
}

TEST(InterfaceItemsParsing, InterfaceGenerateRegion) {
  auto r = Parse(
      "interface ifc;\n"
      "  generate\n"
      "    wire w;\n"
      "  endgenerate\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceItemsParsing, InterfaceNestedProgram) {
  auto r = Parse(
      "interface ifc;\n"
      "  program prg;\n"
      "  endprogram\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceItemsParsing, InterfaceNestedInterface) {
  auto r = Parse(
      "interface outer_ifc;\n"
      "  interface inner_ifc;\n"
      "  endinterface\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceItemsParsing, InterfaceTimeunits) {
  auto r = Parse(
      "interface ifc;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceItemsParsing, InterfaceAlways) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic clk;\n"
      "  always #5 clk = ~clk;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceItemsParsing, InterfaceInitial) {
  auto r = Parse(
      "interface ifc;\n"
      "  initial begin end\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->interfaces[0]->items, ModuleItemKind::kInitialBlock));
}

TEST(InterfaceItemsParsing, InterfaceAssertProperty) {
  auto r = Parse(
      "interface ifc;\n"
      "  assert property (@(posedge clk) req |-> ack);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceItemsParsing, InterfaceItemPortDecl) {
  auto r = Parse(
      "interface ifc(input logic clk, output logic data);\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->interfaces[0]->ports[0].name, "clk");
  EXPECT_EQ(r.cu->interfaces[0]->ports[1].name, "data");
}

TEST(InterfaceItemsParsing, MixedItemTypesParse) {
  EXPECT_TRUE(
      ParseOk("interface ifc #(parameter int W = 8) (input logic clk);\n"
              "  localparam int DEPTH = 4;\n"
              "  logic [W-1:0] data;\n"
              "  wire valid;\n"
              "  function automatic int xform(int v); return v; endfunction\n"
              "  task send; endtask\n"
              "  assign valid = |data;\n"
              "  modport master(output data, input valid);\n"
              "  modport slave(input data, output valid);\n"
              "endinterface\n"));
}

TEST(InterfaceItemsParsing, ExternFunctionPrototypeInInterface) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern function void compute(input int x);\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto* ifc = r.cu->interfaces[0];
  ASSERT_GE(ifc->items.size(), 1u);
  EXPECT_EQ(ifc->items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(ifc->items[0]->name, "compute");
  EXPECT_TRUE(ifc->items[0]->is_extern);

  EXPECT_TRUE(ifc->items[0]->func_body_stmts.empty());
}

TEST(InterfaceItemsParsing, ExternTaskPrototypeInInterface) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern task run();\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto* ifc = r.cu->interfaces[0];
  ASSERT_GE(ifc->items.size(), 1u);
  EXPECT_EQ(ifc->items[0]->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(ifc->items[0]->name, "run");
  EXPECT_TRUE(ifc->items[0]->is_extern);
  EXPECT_TRUE(ifc->items[0]->func_body_stmts.empty());
}

TEST(InterfaceItemsParsing, FunctionDeclaration) {
  auto r = Parse(
      "interface ifc;\n"
      "  function automatic int transform(int val);\n"
      "    return val + 1;\n"
      "  endfunction\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->interfaces[0]->items, ModuleItemKind::kFunctionDecl));
}

TEST(InterfaceItemsParsing, TaskDeclaration) {
  auto r = Parse(
      "interface ifc;\n"
      "  task do_transfer;\n"
      "  endtask\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->interfaces[0]->items, ModuleItemKind::kTaskDecl));
}

TEST(InterfaceItemsParsing, ExternForkjoinTaskPrototype) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern forkjoin task parallel_run();\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto* ifc = r.cu->interfaces[0];
  ASSERT_GE(ifc->items.size(), 1u);
  EXPECT_EQ(ifc->items[0]->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(ifc->items[0]->name, "parallel_run");
  EXPECT_TRUE(ifc->items[0]->is_extern);
  EXPECT_TRUE(ifc->items[0]->is_forkjoin);
  EXPECT_TRUE(ifc->items[0]->func_body_stmts.empty());
}

TEST(InterfaceItemsParsing, EmptyInterfaceBody) {
  auto r = Parse("interface ifc;\nendinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_TRUE(r.cu->interfaces[0]->items.empty());
  EXPECT_TRUE(r.cu->interfaces[0]->modports.empty());
}

TEST(InterfaceItemsParsing, BareSemicolonsIgnored) {
  auto r = Parse(
      "interface ifc;\n"
      "  ;\n"
      "  ;\n"
      "  logic x;\n"
      "  ;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
}

TEST(InterfaceItemsParsing, ExternFunctionNonVoidReturn) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern function int compute();\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func =
      FindItemByKind(r.cu->interfaces[0]->items, ModuleItemKind::kFunctionDecl);
  ASSERT_NE(func, nullptr);
  EXPECT_EQ(func->name, "compute");
  EXPECT_TRUE(func->is_extern);
  EXPECT_TRUE(func->func_body_stmts.empty());
}

TEST(InterfaceItemsParsing, ExternTaskWithParameters) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern task execute(input int addr, output int data);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* task =
      FindItemByKind(r.cu->interfaces[0]->items, ModuleItemKind::kTaskDecl);
  ASSERT_NE(task, nullptr);
  EXPECT_EQ(task->name, "execute");
  EXPECT_TRUE(task->is_extern);
  EXPECT_TRUE(task->func_body_stmts.empty());
}

TEST(InterfaceItemsParsing, ExternForkjoinTaskWithParameters) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern forkjoin task par_exec(input int id);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* task =
      FindItemByKind(r.cu->interfaces[0]->items, ModuleItemKind::kTaskDecl);
  ASSERT_NE(task, nullptr);
  EXPECT_EQ(task->name, "par_exec");
  EXPECT_TRUE(task->is_extern);
  EXPECT_TRUE(task->is_forkjoin);
  EXPECT_TRUE(task->func_body_stmts.empty());
}

TEST(InterfaceItemsParsing, ExternTaskNotForkjoin) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern task plain_run();\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* task =
      FindItemByKind(r.cu->interfaces[0]->items, ModuleItemKind::kTaskDecl);
  ASSERT_NE(task, nullptr);
  EXPECT_TRUE(task->is_extern);
  EXPECT_FALSE(task->is_forkjoin);
}

TEST(InterfaceItemsParsing, AttributeOnModuleCommonItem) {
  auto r = Parse(
      "interface ifc;\n"
      "  (* keep *) wire w;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->interfaces[0]->items.size(), 1u);
  EXPECT_TRUE(HasAttrNamed(r.cu->interfaces[0]->items, "keep"));
}

TEST(InterfaceItemsParsing, AttributeOnExternTfDeclaration) {
  auto r = Parse(
      "interface ifc;\n"
      "  (* synthesis *) extern function void process();\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func =
      FindItemByKind(r.cu->interfaces[0]->items, ModuleItemKind::kFunctionDecl);
  ASSERT_NE(func, nullptr);
  EXPECT_TRUE(func->is_extern);
  EXPECT_TRUE(HasAttrNamed(r.cu->interfaces[0]->items, "synthesis"));
}

TEST(InterfaceItemsParsing, MultipleExternPrototypes) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern function void f1();\n"
      "  extern function int f2(input int a);\n"
      "  extern task t1();\n"
      "  extern forkjoin task t2();\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ifc = r.cu->interfaces[0];
  EXPECT_EQ(
      CountItemsByKind(ifc->items, ModuleItemKind::kFunctionDecl), 2u);
  EXPECT_EQ(
      CountItemsByKind(ifc->items, ModuleItemKind::kTaskDecl), 2u);
}

TEST(InterfaceItemsParsing, AlwaysCombInInterface) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic a, b;\n"
      "  always_comb b = a;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->interfaces[0]->items,
                            ModuleItemKind::kAlwaysCombBlock));
}

TEST(InterfaceItemsParsing, AlwaysFFInInterface) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic clk, q, d;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->interfaces[0]->items,
                            ModuleItemKind::kAlwaysFFBlock));
}

TEST(InterfaceItemsParsing, AlwaysLatchInInterface) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic en, d, q;\n"
      "  always_latch if (en) q <= d;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->interfaces[0]->items,
                            ModuleItemKind::kAlwaysLatchBlock));
}

TEST(InterfaceItemsParsing, FinalBlockInInterface) {
  auto r = Parse(
      "interface ifc;\n"
      "  final begin end\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->interfaces[0]->items, ModuleItemKind::kFinalBlock));
}

TEST(InterfaceItemsParsing, InvalidTokenInBodyIsError) {
  auto r = Parse(
      "interface ifc;\n"
      "  123bad\n"
      "endinterface\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(InterfaceInstantiationGrammar, MultipleInterfaceInstances) {
  auto r = Parse("module m; my_if u0(.a(a)), u1(.a(b)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* i0 = r.cu->modules[0]->items[0];
  auto* i1 = r.cu->modules[0]->items[1];
  EXPECT_EQ(i0->inst_module, "my_if");
  EXPECT_EQ(i0->inst_name, "u0");
  EXPECT_EQ(i1->inst_module, "my_if");
  EXPECT_EQ(i1->inst_name, "u1");
}

TEST(InterfaceInstantiationGrammar, InterfaceInstEmptyPorts) {
  auto r = Parse("module m; my_if u0(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_TRUE(item->inst_ports.empty());
}

TEST(InterfaceInstantiationGrammar, InterfaceInstInsideInterface) {
  auto r = Parse(
      "interface outer_if;\n"
      "  inner_if u0(.clk(clk));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_GE(r.cu->interfaces[0]->items.size(), 1u);
  auto* item = r.cu->interfaces[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "inner_if");
  EXPECT_EQ(item->inst_name, "u0");
}

TEST(InterfaceInstantiationGrammar, BasicInterfaceInst) {
  auto r = Parse("module m; my_if u0(.a(a), .b(b)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_if");
  EXPECT_EQ(item->inst_name, "u0");
}

TEST(InterfaceInstantiationGrammar, InterfaceInstWithParams) {
  auto r = Parse("module m; my_if #(8) u0(.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_if");
  EXPECT_EQ(item->inst_name, "u0");
  ASSERT_EQ(item->inst_params.size(), 1u);
}

TEST(InterfaceInstantiationGrammar, InterfaceInstWithNamedParams) {
  auto r = Parse("module m; my_if #(.W(16)) u0(.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_if");
  ASSERT_EQ(item->inst_params.size(), 1u);
  EXPECT_EQ(item->inst_params[0].first, "W");
}

TEST(InterfaceInstantiationGrammar, InterfaceInstInModule) {
  EXPECT_TRUE(
      ParseOk("interface simple_bus(input logic clk);\n"
              "  logic req, gnt;\n"
              "endinterface\n"
              "module top;\n"
              "  logic clk;\n"
              "  simple_bus sb_intf(.clk(clk));\n"
              "endmodule\n"));
}

TEST(InterfaceInstantiationGrammar, ModuleInstantiatesInterface) {
  EXPECT_TRUE(
      ParseOk("interface ifc; logic req; endinterface\n"
              "module m;\n"
              "  ifc u0();\n"
              "endmodule\n"));
}

TEST(InterfaceInstantiationGrammar, InterfaceInstEmptyParam) {
  auto r = Parse("module m; my_if #() u0(.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_if");
  EXPECT_TRUE(item->inst_params.empty());
}

TEST(InterfaceInstantiationGrammar, InterfaceInstOrderedPorts) {
  auto r = Parse("module m; my_if u0(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 3u);
}

TEST(InterfaceInstantiationGrammar, InterfaceInstNamedPortNoParens) {
  auto r = Parse("module m; my_if u0(.clk, .rst); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "rst");
}

TEST(InterfaceInstantiationGrammar, InterfaceInstWildcardPort) {
  auto r = Parse("module m; my_if u0(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
}

TEST(InterfaceInstantiationGrammar, InterfaceInstArray) {
  auto r = Parse("module m; my_if u0 [3:0] (.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_if");
  EXPECT_NE(item->inst_range_left, nullptr);
  EXPECT_NE(item->inst_range_right, nullptr);
}

TEST(InterfaceInstantiationGrammar, MultipleInstancesWithParams) {
  auto r = Parse(
      "module m; my_if #(.W(8)) u0(.a(a)), u1(.a(b)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* i0 = r.cu->modules[0]->items[0];
  auto* i1 = r.cu->modules[0]->items[1];
  EXPECT_EQ(i0->inst_module, "my_if");
  EXPECT_EQ(i0->inst_name, "u0");
  ASSERT_EQ(i0->inst_params.size(), 1u);
  EXPECT_EQ(i0->inst_params[0].first, "W");
  EXPECT_EQ(i1->inst_module, "my_if");
  EXPECT_EQ(i1->inst_name, "u1");
}

TEST(InterfaceInstantiationGrammar, ThreeCommaSeparatedInstances) {
  auto r = Parse("module m; my_if u0(), u1(), u2(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->inst_name, "u0");
  EXPECT_EQ(r.cu->modules[0]->items[1]->inst_name, "u1");
  EXPECT_EQ(r.cu->modules[0]->items[2]->inst_name, "u2");
}

TEST(InterfaceInstantiationGrammar, ParamsWithEmptyPorts) {
  auto r = Parse("module m; my_if #(8) u0(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_if");
  ASSERT_EQ(item->inst_params.size(), 1u);
  EXPECT_TRUE(item->inst_ports.empty());
}

TEST(InterfaceInstantiationGrammar, MissingSemicolonIsError) {
  EXPECT_FALSE(ParseOk("module m; my_if u0() endmodule\n"));
}

TEST(InterfaceItemsParsing, NestedProgramInInterface) {
  auto r = Parse(
      "interface bus;\n"
      "  program p;\n"
      "    initial $display(\"bus\");\n"
      "  endprogram\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_TRUE(HasItemOfKind(r.cu->interfaces[0]->items,
                            ModuleItemKind::kNestedModuleDecl));
}

TEST(InterfaceInstantiationGrammar, ScalarAndVectorInstancesFromLrm) {
  auto r = Parse(
      "module m; myinterface #(100) scalar1(), vector[9:0](); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* scalar = r.cu->modules[0]->items[0];
  auto* vector = r.cu->modules[0]->items[1];
  EXPECT_EQ(scalar->inst_module, "myinterface");
  EXPECT_EQ(scalar->inst_name, "scalar1");
  EXPECT_EQ(scalar->inst_range_left, nullptr);
  EXPECT_EQ(vector->inst_module, "myinterface");
  EXPECT_EQ(vector->inst_name, "vector");
  EXPECT_NE(vector->inst_range_left, nullptr);
  EXPECT_NE(vector->inst_range_right, nullptr);
  ASSERT_EQ(scalar->inst_params.size(), 1u);
  ASSERT_EQ(vector->inst_params.size(), 1u);
}

TEST(InterfaceParsing, PackageImportInNonAnsiHeader) {
  EXPECT_TRUE(
      ParseOk("package pkg; typedef int t; endpackage\n"
              "interface ifc import pkg::*; (clk);\n"
              "  input clk;\n"
              "endinterface\n"));
}

TEST(InterfaceParsing, PackageImportInAnsiHeaderWithPortDecls) {
  EXPECT_TRUE(
      ParseOk("package pkg; typedef int t; endpackage\n"
              "interface ifc import pkg::*; (input logic clk);\n"
              "endinterface\n"));
}

TEST(InterfaceParsing, PackageImportInAnsiHeaderWithParamPortList) {
  EXPECT_TRUE(
      ParseOk("package pkg; parameter int W = 8; endpackage\n"
              "interface ifc import pkg::*; #(parameter int N = 4) ();\n"
              "endinterface\n"));
}

TEST(InterfaceParsing, ExternNonAnsiHeader) {
  auto r = Parse("extern interface ifc(clk);\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_TRUE(r.cu->interfaces[0]->is_extern);
  EXPECT_EQ(r.cu->interfaces[0]->name, "ifc");
}

TEST(InterfaceItemsParsing, RepeatedTimeunitsMatchingIsAllowed) {
  EXPECT_TRUE(
      ParseOk("timeunit 1ns;\n"
              "interface ifc;\n"
              "  timeunit 1ns;\n"
              "endinterface\n"));
}

TEST(InterfaceItemsParsing, ModuleDeclInsideInterface) {
  auto r = Parse(
      "interface ifc;\n"
      "  module nested_mod;\n"
      "  endmodule\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_TRUE(HasItemOfKind(r.cu->interfaces[0]->items,
                            ModuleItemKind::kNestedModuleDecl));
}

}  // namespace
