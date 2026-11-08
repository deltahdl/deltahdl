#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

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

TEST(InterfaceItemsParsing, ExternForkjoinFunctionIsError) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern forkjoin function int compute();\n"
      "endinterface\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'task', got 'function'", 2, "13.3"));
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

void ExpectSoleModportPrototype(const std::string& src, bool is_export,
                                ModuleItemKind kind, std::string_view name) {
  auto r = Parse(src);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto* mp = r.cu->interfaces[0]->modports[0];
  ASSERT_EQ(mp->ports.size(), 1u);
  EXPECT_EQ(mp->ports[0].is_export, is_export);
  EXPECT_EQ(mp->ports[0].is_import, !is_export);
  ASSERT_NE(mp->ports[0].prototype, nullptr);
  EXPECT_EQ(mp->ports[0].prototype->kind, kind);
  EXPECT_EQ(mp->ports[0].prototype->name, name);
}

TEST(ModportDeclarationParsing, ModportImportFunctionPrototype) {
  ExpectSoleModportPrototype(
      "interface ifc;\n"
      "  modport mp(import function int compute(int a));\n"
      "endinterface\n",
      false, ModuleItemKind::kFunctionDecl, "compute");
}

TEST(ModportDeclarationParsing, ImportTaskPrototype) {
  ExpectSoleModportPrototype(
      "interface bus;\n"
      "  modport init(import task Read(input logic [7:0] raddr));\n"
      "endinterface\n",
      false, ModuleItemKind::kTaskDecl, "Read");
}

TEST(ModportDeclarationParsing, ExportFunctionPrototype) {
  ExpectSoleModportPrototype(
      "interface ifc;\n"
      "  modport mp(export function void compute(int a));\n"
      "endinterface\n",
      true, ModuleItemKind::kFunctionDecl, "compute");
}

TEST(ModportDeclarationParsing, ExportTaskPrototype) {
  ExpectSoleModportPrototype(
      "interface ifc;\n"
      "  modport mp(export task Write(input logic [7:0] waddr));\n"
      "endinterface\n",
      true, ModuleItemKind::kTaskDecl, "Write");
}

TEST(InterfaceItemsParsing, ExternFunctionPrototypeReturnType) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern function int compute(input int a);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func =
      FindItemByKind(r.cu->interfaces[0]->items, ModuleItemKind::kFunctionDecl);
  ASSERT_NE(func, nullptr);
  EXPECT_TRUE(func->is_extern);
  EXPECT_EQ(func->return_type.kind, DataTypeKind::kInt);
}

}  // namespace
