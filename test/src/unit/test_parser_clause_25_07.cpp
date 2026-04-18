#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(TaskDeclParsing, TaskBodyInterfaceScope) {
  auto r = Parse(
      "interface intf;\n"
      "  extern task my_task();\n"
      "endinterface\n"
      "task intf.my_task();\n"
      "endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
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

TEST(ModportDeclarationParsing, AttrOnImportPort) {
  EXPECT_TRUE(
      ParseOk("interface bus;\n"
              "  modport target((* synthesis *) import Read);\n"
              "endinterface\n"));
}

TEST(ModportDeclarationParsing, ModportTfPortsImportIdentifier) {
  auto r = Parse(
      "interface ifc;\n"
      "  modport mp(import my_func);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_GE(mp->ports.size(), 1u);
  VerifyImportExportPort(mp->ports[0], true, false, "my_func");
}

TEST(ModportDeclarationParsing, ModportTfPortsExportIdentifier) {
  auto r = Parse(
      "interface ifc;\n"
      "  modport mp(export my_task);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_GE(mp->ports.size(), 1u);
  VerifyImportExportPort(mp->ports[0], false, true, "my_task");
}

TEST(ModportDeclarationParsing, ImportMultipleIdentifiers) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(import Read, Write);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2u);
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_EQ(mp->ports[0].name, "Read");
  EXPECT_TRUE(mp->ports[1].is_import);
  EXPECT_EQ(mp->ports[1].name, "Write");
}

TEST(ModportDeclarationParsing, ImportSingleIdentifier) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(import Read);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_EQ(mp->ports[0].name, "Read");
}

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

TEST(ModportDeclarationParsing, ImportFlagNotExport) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(import Read);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_FALSE(mp->ports[0].is_export);
}

TEST(ModportDeclarationParsing, ExportSingleIdentifier) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(export Write);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_export);
  EXPECT_EQ(mp->ports[0].name, "Write");
}

TEST(ModportDeclarationParsing, ExportMultipleIdentifiers) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(export Read, Write);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2u);
  EXPECT_TRUE(mp->ports[0].is_export);
  EXPECT_EQ(mp->ports[0].name, "Read");
  EXPECT_TRUE(mp->ports[1].is_export);
  EXPECT_EQ(mp->ports[1].name, "Write");
}

TEST(ModportDeclarationParsing, ExportFlagNotImport) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(export Write);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  EXPECT_FALSE(mp->ports[0].is_import);
  EXPECT_TRUE(mp->ports[0].is_export);
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

TEST(ModportDeclarationParsing, ModportImportTaskPrototype) {
  auto r = Parse(
      "interface ifc;\n"
      "  modport mp(import task do_work(int x));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_GE(mp->ports.size(), 1u);
  EXPECT_TRUE(mp->ports[0].is_import);
  ASSERT_NE(mp->ports[0].prototype, nullptr);
  EXPECT_EQ(mp->ports[0].prototype->kind, ModuleItemKind::kTaskDecl);
}

TEST(ModportDeclarationParsing, ImportTaskNoArgs) {
  auto r = Parse(
      "interface bus;\n"
      "  modport target(import task doWork);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_NE(mp->ports[0].prototype, nullptr);
  EXPECT_EQ(mp->ports[0].prototype->name, "doWork");
}

TEST(ModportDeclarationParsing, ImportFunctionVoidReturn) {
  EXPECT_TRUE(
      ParseOk("interface bus;\n"
              "  modport init(import function void reset());\n"
              "endinterface\n"));
}

TEST(ModportDeclarationParsing, FunctionPrototypeReturnType) {
  auto r = Parse(
      "interface bus;\n"
      "  modport init(import function int compute(input int a));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  ASSERT_NE(mp->ports[0].prototype, nullptr);
  EXPECT_EQ(mp->ports[0].prototype->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(mp->ports[0].prototype->data_type.kind, DataTypeKind::kInt);
}

TEST(ModportDeclarationParsing, TaskPrototypeHasArgs) {
  auto r = Parse(
      "interface bus;\n"
      "  modport init(import task Read(input logic [7:0] raddr));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_NE(mp->ports[0].prototype, nullptr);
  EXPECT_FALSE(mp->ports[0].prototype->func_args.empty());
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

TEST(ModportDeclarationParsing, ExportTaskPrototype) {
  EXPECT_TRUE(
      ParseOk("interface bus;\n"
              "  modport target(export task Read(input logic [7:0] addr));\n"
              "endinterface\n"));
}

TEST(ModportDeclarationParsing, ImportMultiplePrototypes) {
  auto r = Parse(
      "interface bus;\n"
      "  modport init(\n"
      "    import task Read(input logic [7:0] raddr),\n"
      "           task Write(input logic [7:0] waddr)\n"
      "  );\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 2u);
  EXPECT_TRUE(mp->ports[0].is_import);
  EXPECT_EQ(mp->ports[0].prototype->name, "Read");
  EXPECT_TRUE(mp->ports[1].is_import);
  EXPECT_EQ(mp->ports[1].prototype->name, "Write");
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

TEST(ModportDeclarationParsing, AttrOnExportPort) {
  EXPECT_TRUE(
      ParseOk("interface ifc;\n"
              "  modport mp((* synthesis *) export Write);\n"
              "endinterface\n"));
}

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

TEST(InterfaceItemsParsing, ExternTaskWithDefaultArg) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern task run(input int n = 1);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* task =
      FindItemByKind(r.cu->interfaces[0]->items, ModuleItemKind::kTaskDecl);
  ASSERT_NE(task, nullptr);
  ASSERT_EQ(task->func_args.size(), 1u);
  EXPECT_NE(task->func_args[0].default_value, nullptr);
}

TEST(ModportDeclarationParsing, ImportFunctionPrototypeWithDefaultArg) {
  auto r = Parse(
      "interface ifc;\n"
      "  modport mp(import function int compute(int a = 0));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_GE(mp->ports.size(), 1u);
  ASSERT_NE(mp->ports[0].prototype, nullptr);
  ASSERT_EQ(mp->ports[0].prototype->func_args.size(), 1u);
  EXPECT_NE(mp->ports[0].prototype->func_args[0].default_value, nullptr);
}

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

TEST(FunctionDeclParsing, HierarchicalFunctionBody) {
  auto r = Parse(
      "interface intf;\n"
      "  extern function int my_func(input int a);\n"
      "endinterface\n"
      "function int intf.my_func(input int a);\n"
      "  return a;\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(InterfaceItemsParsing, ExternForkjoinFunctionIsError) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern forkjoin function int compute();\n"
      "endinterface\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
