#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

TEST(InterfaceItemsParsing, ExternMethodPrototype) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern function void work();\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func =
      FindItemByKind(r.cu->interfaces[0]->items, ModuleItemKind::kFunctionDecl);
  ASSERT_NE(func, nullptr);
  EXPECT_TRUE(func->is_extern);
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

TEST(InterfaceItemsParsing, ModportDeclaration) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic data;\n"
      "  modport master(output data);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->interfaces[0]->modports.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->modports[0]->name, "master");
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

TEST(InterfaceItemsParsing, InterfacePortDecl) {
  auto r = Parse(
      "interface ifc(a, b);\n"
      "  input a;\n"
      "  output b;\n"
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

TEST(InterfaceItemsParsing, InterfaceOrGenerateItemModuleCommon) {
  auto r = Parse(
      "interface ifc;\n"
      "  assign a = b;\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto* ifc = r.cu->interfaces[0];
  ASSERT_GE(ifc->items.size(), 1u);
  EXPECT_EQ(ifc->items[0]->kind, ModuleItemKind::kContAssign);
}

TEST(InterfaceItemsParsing, NonPortInterfaceItemGenerateRegion) {
  auto r = Parse(
      "interface ifc;\n"
      "  generate\n"
      "    assign a = b;\n"
      "  endgenerate\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_GE(r.cu->interfaces[0]->items.size(), 1u);
}

TEST(InterfaceItemsParsing, NonPortInterfaceItemProgram) {
  auto r = Parse(
      "interface ifc;\n"
      "  program p; endprogram\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_GE(r.cu->interfaces[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->items[0]->kind,
            ModuleItemKind::kNestedModuleDecl);
}

TEST(InterfaceItemsParsing, NonPortInterfaceItemNestedInterface) {
  auto r = Parse(
      "interface outer;\n"
      "  interface inner; endinterface\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_GE(r.cu->interfaces[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->items[0]->kind,
            ModuleItemKind::kNestedModuleDecl);
}

TEST(InterfaceItemsParsing, NonPortInterfaceItemTimeunits) {
  auto r = Parse(
      "interface ifc;\n"
      "  timeunit 1ns;\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
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

TEST(InterfaceItemsParsing, NonPortInterfaceItemModport) {
  auto r = Parse(
      "interface ifc;\n"
      "  modport master(input clk, output data);\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->modports[0]->name, "master");
}

TEST(InterfaceItemsParsing, WithInitialBlock) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic flag;\n"
      "  initial flag = 0;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->interfaces[0]->items, ModuleItemKind::kInitialBlock));
}

TEST(InterfaceItemsParsing, WithAlwaysBlock) {
  EXPECT_TRUE(
      ParseOk("interface ifc;\n"
              "  logic clk, gnt, req;\n"
              "  always @(posedge clk) gnt <= req;\n"
              "endinterface\n"));
}

TEST(InterfaceItemsParsing, WithContAssign) {
  auto r = Parse(
      "interface ifc;\n"
      "  logic a;\n"
      "  wire b;\n"
      "  assign b = a;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->interfaces[0]->items, ModuleItemKind::kContAssign));
}

TEST(InterfaceItemsParsing, WithMixedContents) {
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

TEST(InterfaceItemsParsing, WithFunction) {
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

TEST(InterfaceItemsParsing, WithTask) {
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

// --- Missing tests below ---

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

}  // namespace
