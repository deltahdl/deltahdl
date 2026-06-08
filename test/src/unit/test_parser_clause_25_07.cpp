#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §25.7: a function defined elsewhere is named in the interface by an extern
// prototype that carries no body.
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

// §25.7: a task prototype likewise names a task defined elsewhere.
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

// §25.7: subroutines may also be defined directly within an interface.
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

// §25.7: a prototype records the directions of its formal arguments.
TEST(InterfaceItemsParsing, ExternTaskAllArgDirections) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern task run(input int i, output int o, inout int io, ref int r);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* task =
      FindItemByKind(r.cu->interfaces[0]->items, ModuleItemKind::kTaskDecl);
  ASSERT_NE(task, nullptr);
  ASSERT_EQ(task->func_args.size(), 4u);
  EXPECT_EQ(task->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(task->func_args[1].direction, Direction::kOutput);
  EXPECT_EQ(task->func_args[2].direction, Direction::kInout);
  EXPECT_EQ(task->func_args[3].direction, Direction::kRef);
}

// §25.7: a prototype may carry a default argument value.
TEST(InterfaceItemsParsing, ExternFunctionWithDefaultArg) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern function int compute(input int a, input int b = 7);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func =
      FindItemByKind(r.cu->interfaces[0]->items, ModuleItemKind::kFunctionDecl);
  ASSERT_NE(func, nullptr);
  ASSERT_EQ(func->func_args.size(), 2u);
  EXPECT_EQ(func->func_args[0].default_value, nullptr);
  EXPECT_NE(func->func_args[1].default_value, nullptr);
}

// §25.7: a task that may be defined in more than one connected module is
// declared with the extern forkjoin keywords.
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

// §25.7: forkjoin applies to tasks only — a forkjoin function is rejected.
TEST(InterfaceItemsParsing, ExternForkjoinFunctionIsError) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern forkjoin function int compute();\n"
      "endinterface\n");
  EXPECT_TRUE(r.has_errors);
}

// §25.7: a subroutine declared extern in an interface may be defined out of
// block using a hierarchical name.
TEST(TaskDeclParsing, HierarchicalTaskBodyWithArgs) {
  auto r = Parse(
      "interface intf;\n"
      "  extern task my_task(input int x, output int y);\n"
      "endinterface\n"
      "task intf.my_task(input int x, output int y);\n"
      "  y = x;\n"
      "endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §25.7: in a modport, subroutines are made accessible with import and export
// items, named either by a bare identifier or by a full prototype.
TEST(ModportDeclarationParsing, ImportExportPortsVerified) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(import Read, export Write);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2);
  VerifyImportExportPort(mp->ports[0], true, false, "Read");
  VerifyImportExportPort(mp->ports[1], false, true, "Write");
}

TEST(ModportDeclarationParsing, ModportImportFunctionPrototype) {
  auto r = Parse(
      "interface ifc;\n"
      "  modport mp(import function int compute(int a));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_GE(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_import);
  ASSERT_NE(mp->ports[0].prototype, nullptr);
  EXPECT_EQ(mp->ports[0].prototype->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(mp->ports[0].prototype->name, "compute");
}

TEST(ModportDeclarationParsing, ImportTaskPrototype) {
  auto r = Parse(
      "interface bus;\n"
      "  modport init(import task Read(input logic [7:0] raddr));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_NE(mp->ports[0].prototype, nullptr);
  EXPECT_EQ(mp->ports[0].prototype->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(mp->ports[0].prototype->name, "Read");
}

TEST(ModportDeclarationParsing, ExportFunctionPrototype) {
  auto r = Parse(
      "interface ifc;\n"
      "  modport mp(export function void compute(int a));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_export);
  EXPECT_FALSE(mp->ports[0].is_import);
  ASSERT_NE(mp->ports[0].prototype, nullptr);
  EXPECT_EQ(mp->ports[0].prototype->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(mp->ports[0].prototype->name, "compute");
}

}
