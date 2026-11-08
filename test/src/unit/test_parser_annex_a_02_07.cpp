#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(TaskDeclParsing, TaskDeclNoLifetime) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_FALSE(item->is_automatic);
  EXPECT_FALSE(item->is_static);
  EXPECT_EQ(item->name, "my_task");
}

TEST(TaskDeclParsing, TaskBodyNewStyleBlockItemDecl) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input int x);\n"
      "    int temp;\n"
      "    temp = x + 1;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_GE(item->func_body_stmts.size(), 1u);
}

TEST(TaskDeclParsing, TaskBodyWithStatements) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input int x);\n"
      "    #10;\n"
      "    $display(\"x=%0d\", x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_GE(item->func_body_stmts.size(), 2u);
}

TEST(TaskDeclParsing, TaskBodyOldStyleMixedDirectionPorts) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "    input int a;\n"
      "    output int b;\n"
      "    b = a + 1;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].direction, Direction::kOutput);
}

TEST(TaskDeclParsing, TaskBodyPortOfAPackageScopedType) {
  auto r = Parse(
      "package pk;\n"
      "  typedef logic [3:0] t;\n"
      "endpackage\n"
      "module m;\n"
      "  task my_task;\n"
      "    input pk::t a;\n"
      "    output var pk::t b;\n"
      "    b = a;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  for (const auto& arg : item->func_args) {
    EXPECT_EQ(arg.data_type.scope_name, "pk");
    EXPECT_EQ(arg.data_type.type_name, "t");
  }
}

TEST(TaskDeclParsing, TaskBodyWithEndLabelNoPortList) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "  endtask : my_task\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "my_task");
}

TEST(TaskDeclParsing, TaskBodyInterfaceScope) {
  auto r = Parse(
      "module m;\n"
      "  task ifc.my_task;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(item->name, "my_task");
}

TEST(TaskDeclParsing, TaskBodyEmptyNoPortsNoStatements) {
  auto r = Parse(
      "module m;\n"
      "  task empty_task;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->func_args.empty());
  EXPECT_TRUE(item->func_body_stmts.empty());
}

TEST(TaskDeclParsing, TfItemDeclMixedPortsAndVars) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "    input int a;\n"
      "    output int b;\n"
      "    int temp;\n"
      "    temp = a;\n"
      "    b = temp;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_GE(item->func_body_stmts.size(), 2u);
}

TEST(TaskDeclParsing, TfPortListMultiplePorts) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input int a, input int b, output int c);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 3u);
  EXPECT_EQ(item->func_args[0].name, "a");
  EXPECT_EQ(item->func_args[1].name, "b");
  EXPECT_EQ(item->func_args[2].name, "c");
}

TEST(TaskDeclParsing, TfPortItemVar) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(var int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "x");
}

TEST(TaskDeclParsing, TfPortItemWithDefaultValue) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input int x = 42);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_NE(item->func_args[0].default_value, nullptr);
}

TEST(TaskDeclParsing, TfPortItemWithUnpackedDims) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input int x [3]);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_FALSE(item->func_args[0].unpacked_dims.empty());
}

TEST(TaskDeclParsing, TfPortItemNoIdentifier) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern task my_task(input int);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->interfaces[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
}

TEST(TaskDeclParsing, TfPortDirectionInput) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input logic a);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->func_args[0].direction,
            Direction::kInput);
}

TEST(TaskDeclParsing, TfPortDirectionOutput) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(output logic a);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->func_args[0].direction,
            Direction::kOutput);
}

TEST(TaskDeclParsing, TfPortDirectionInout) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(inout logic a);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->func_args[0].direction,
            Direction::kInout);
}

TEST(TaskDeclParsing, TfPortDirectionRef) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(ref int a);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->func_args[0].direction,
            Direction::kRef);
}

TEST(TaskDeclParsing, TfPortDirectionConstRef) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(const ref int a);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
}

TEST(TaskDeclParsing, TfPortDirectionRefStatic) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  task my_task(ref static int a);\n"
              "  endtask\n"
              "endmodule\n"));
}

TEST(TaskDeclParsing, TfPortDeclOldStyleVar) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "    input var int x;\n"
      "    $display(\"%0d\", x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
}

TEST(TaskDeclParsing, TfPortDeclOutput) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "    output int y;\n"
      "    y = 1;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kOutput);
  EXPECT_EQ(item->func_args[0].name, "y");
}

TEST(TaskDeclParsing, TfPortDeclMultipleIdentifiers) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "    input int a, b, c;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 3u);
  EXPECT_EQ(item->func_args[0].name, "a");
  EXPECT_EQ(item->func_args[1].name, "b");
  EXPECT_EQ(item->func_args[2].name, "c");
}

TEST(TaskDeclParsing, TfPortDeclConstRef) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "    const ref int x;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
}

TEST(TaskDeclParsing, ConstWithoutRefIsNotATfPortDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input int a);\n"
      "    const int c = a + 1;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].name, "a");
  ASSERT_EQ(item->func_body_stmts.size(), 1u);
  EXPECT_EQ(item->func_body_stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(item->func_body_stmts[0]->var_is_const);
  EXPECT_NE(item->func_body_stmts[0]->var_init, nullptr);
}

TEST(TaskDeclParsing, TfPortDeclWithDefaultValue) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "    input int x = 10;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_NE(item->func_args[0].default_value, nullptr);
}

TEST(TaskDeclParsing, TaskPrototypeWithArgs) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern task my_task(input int x);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->interfaces[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_extern);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_TRUE(item->func_body_stmts.empty());
}

TEST(TaskDeclParsing, TaskPrototypeEmptyParens) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern task my_task();\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->interfaces[0]->items[0];
  EXPECT_TRUE(item->is_extern);
  EXPECT_TRUE(item->func_args.empty());
}

TEST(TaskDeclParsing, TaskPrototypeNoParens) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern task my_task;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->interfaces[0]->items[0];
  EXPECT_TRUE(item->is_extern);
  EXPECT_TRUE(item->func_args.empty());
}

TEST(TaskDeclParsing, TaskDeclDynOverrideInitial) {
  auto r = Parse(
      "class c;\n"
      "  virtual task :initial my_task;\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* cls = r.cu->classes[0];
  auto* method = cls->members[0]->method;
  EXPECT_TRUE(method->is_method_initial);
  EXPECT_FALSE(method->is_method_extends);
  EXPECT_FALSE(method->is_method_final);
}

TEST(TaskDeclParsing, TaskDeclDynOverrideExtends) {
  auto r = Parse(
      "class c;\n"
      "  virtual task :extends my_task;\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* method = r.cu->classes[0]->members[0]->method;
  EXPECT_FALSE(method->is_method_initial);
  EXPECT_TRUE(method->is_method_extends);
}

TEST(TaskDeclParsing, TaskDeclDynOverrideFinal) {
  auto r = Parse(
      "class c;\n"
      "  virtual task :final my_task;\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* method = r.cu->classes[0]->members[0]->method;
  EXPECT_TRUE(method->is_method_final);
}

TEST(TaskDeclParsing, TaskDeclDynOverrideExtendsFinal) {
  auto r = Parse(
      "class c;\n"
      "  virtual task :extends :final my_task;\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* method = r.cu->classes[0]->members[0]->method;
  EXPECT_TRUE(method->is_method_extends);
  EXPECT_TRUE(method->is_method_final);
}

TEST(TaskDeclParsing, TaskDeclDynOverrideInitialFinal) {
  auto r = Parse(
      "class c;\n"
      "  virtual task :initial :final my_task;\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* method = r.cu->classes[0]->members[0]->method;
  EXPECT_TRUE(method->is_method_initial);
  EXPECT_TRUE(method->is_method_final);
}

TEST(TaskDeclParsing, TaskDeclLifetimeAutomatic) {
  auto r = Parse(
      "module m;\n"
      "  task automatic my_task;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_automatic);
  EXPECT_FALSE(item->is_static);
  EXPECT_EQ(item->name, "my_task");
}

TEST(TaskDeclParsing, TaskDeclLifetimeStatic) {
  auto r = Parse(
      "module m;\n"
      "  task static my_task;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_FALSE(item->is_automatic);
  EXPECT_TRUE(item->is_static);
}

TEST(TaskDeclParsing, TaskBodyClassScopeNoPortList) {
  auto r = Parse(
      "class c;\n"
      "  extern task my_task;\n"
      "endclass\n"
      "task c::my_task;\n"
      "endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->cu_items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(item->method_class, "c");
  EXPECT_EQ(item->name, "my_task");
}

TEST(TaskDeclParsing, TfPortItemImplicitDataType) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input a);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[0].name, "a");
}

TEST(TaskDeclParsing, TaskPrototypeWithDynOverride) {
  auto r = Parse(
      "class c;\n"
      "  extern task :final my_task();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* method = r.cu->classes[0]->members[0]->method;
  EXPECT_TRUE(method->is_extern);
  EXPECT_TRUE(method->is_method_final);
  EXPECT_FALSE(method->is_method_initial);
  EXPECT_FALSE(method->is_method_extends);
}

TEST(TaskDeclParsing, TaskBodyAnsiEmptyParens) {
  auto r = Parse(
      "module m;\n"
      "  task my_task();\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->func_args.empty());
}

TEST(TaskDeclParsing, TfPortItemWithAttribute) {
  auto r = Parse(
      "module m;\n"
      "  task my_task((* my_attr *) input int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[0].name, "x");
}

TEST(TaskDeclParsing, TfPortDeclWithAttribute) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "    (* my_attr *) input int x;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[0].name, "x");
}

TEST(TaskDeclParsing, TfPortDirectionConstRefStatic) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(const ref static int a);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_TRUE(item->func_args[0].is_ref_static);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
}

TEST(TaskDeclParsing, ErrorTfPortDirectionInputCombinedWithRef) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input ref int a);\n"
      "  endtask\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "combining ref with another directional qualifier is illegal", 2,
      "13.3"));
}

TEST(TaskDeclParsing, ErrorTfPortDirectionRefCombinedWithInout) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(ref inout int a);\n"
      "  endtask\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "combining ref with another directional qualifier is illegal", 2,
      "13.3"));
}

TEST(TaskDeclParsing, TaskBodyWithNullStatement) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "    ;\n"
      "    ;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_GE(item->func_body_stmts.size(), 2u);
}

TEST(TaskDeclParsing, TaskPrototypeMultiplePorts) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern task my_task(input int a, output int b);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->interfaces[0]->items[0];
  EXPECT_TRUE(item->is_extern);
  ASSERT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].direction, Direction::kOutput);
}

TEST(TaskDeclParsing, ErrorTaskDeclDynOverrideInitialAndExtends) {
  auto r = Parse(
      "class c;\n"
      "  virtual task :initial :extends my_task;\n"
      "  endtask\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "':initial' and ':extends' are mutually exclusive", 2, "8.20"));
}

TEST(TaskDeclParsing, FormalsOfATypeReference) {
  auto r = Parse(
      "module m;\n"
      "  int x;\n"
      "  function automatic int f(input var type(x) y);\n"
      "    return y;\n"
      "  endfunction\n"
      "  function automatic int g;\n"
      "    input var type(x) z;\n"
      "    return z;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  for (const ModuleItem* fn : {items[1], items[2]}) {
    ASSERT_EQ(fn->func_args.size(), 1u) << fn->name;
    EXPECT_NE(fn->func_args[0].data_type.type_ref_expr, nullptr) << fn->name;
  }
}

TEST(TaskDeclParsing, FormalOfATypeReferenceWithoutVarIsReported) {
  auto r = Parse(
      "module m;\n"
      "  int x;\n"
      "  function automatic int h(input type(x) w);\n"
      "    return w;\n"
      "  endfunction\n"
      "  task t;\n"
      "    input type(x) v;\n"
      "  endtask\n"
      "endmodule\n");
  for (uint32_t line : {3U, 7U}) {
    EXPECT_TRUE(
        ReportedError(r.diags,
                      "type_reference in a variable declaration must be "
                      "preceded by the 'var' keyword",
                      line, "6.23"));
  }
}

TEST(TaskDeclParsing, DeclarationAfterAStatementIsReported) {
  auto r = Parse(
      "module m;\n"
      "  task t;\n"
      "    input a;\n"
      "    int n;\n"
      "    $display(a);\n"
      "    int x;\n"
      "  endtask\n"
      "  task u(input int b);\n"
      "    logic k;\n"
      "    ;\n"
      "    localparam int P = 1;\n"
      "    k = b;\n"
      "  endtask\n"
      "endmodule\n");
  const char* msg = "a declaration cannot follow a statement in a task body";
  EXPECT_TRUE(ReportedError(r.diags, msg, 6, "13.3"));
  EXPECT_TRUE(ReportedError(r.diags, msg, 11, "13.3"));
  for (uint32_t line : {4U, 9U}) {
    EXPECT_FALSE(ReportedError(r.diags, msg, line, "13.3"));
  }
}

TEST(TaskDeclParsing, ConstWithoutRefOnAFormalIsReported) {
  auto r = Parse(
      "module m;\n"
      "  task t(const int a);\n"
      "  endtask\n"
      "  function void f(input int x,\n"
      "                  const input int b);\n"
      "  endfunction\n"
      "  task u(const ref int d, e);\n"
      "  endtask\n"
      "endmodule\n");
  const char* msg = "'const' in a formal qualifies only a 'ref' direction";
  for (uint32_t line : {2U, 5U}) {
    EXPECT_TRUE(ReportedError(r.diags, msg, line, "A.2.7"));
  }
  EXPECT_FALSE(ReportedError(r.diags, msg, 7, "A.2.7"));
  ASSERT_NE(r.cu, nullptr);
  const auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  ASSERT_EQ(items[0]->func_args.size(), 1u);
  EXPECT_FALSE(items[0]->func_args[0].is_const);
  ASSERT_EQ(items[2]->func_args.size(), 2u);
  EXPECT_TRUE(items[2]->func_args[0].is_const);
  EXPECT_TRUE(items[2]->func_args[1].is_const);
}

TEST(TaskDeclParsing, NamelessPrototypeFormalTakesNoDimensionOrDefault) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern task t(input int = 5);\n"
      "  extern function void f(input logic [7:0] [4], output byte);\n"
      "  extern task g(input int a = 1);\n"
      "endinterface\n");
  const char* msg =
      "a formal written without a name takes no unpacked dimension and no "
      "default value";
  for (uint32_t line : {2U, 3U}) {
    EXPECT_TRUE(ReportedError(r.diags, msg, line, "A.2.7"));
  }
  EXPECT_FALSE(ReportedError(r.diags, msg, 4, "A.2.7"));
}

TEST(TaskDeclParsing, InterfacePrefixWithAClassScopeIsReported) {
  auto r = Parse(
      "class C;\n"
      "  extern task t;\n"
      "  extern task u;\n"
      "endclass\n"
      "task ifc.C::t;\n"
      "endtask\n"
      "task C::u;\n"
      "endtask\n"
      "module m;\n"
      "  task ifc.v;\n"
      "  endtask\n"
      "endmodule\n");
  const char* msg =
      "a task's name takes an interface prefix or a class scope, not both";
  EXPECT_TRUE(ReportedError(r.diags, msg, 5, "A.2.7"));
  for (uint32_t line : {7U, 10U}) {
    EXPECT_FALSE(ReportedError(r.diags, msg, line, "A.2.7"));
  }
}

}  // namespace
