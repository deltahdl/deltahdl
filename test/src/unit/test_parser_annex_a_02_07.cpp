#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- task_declaration ---

TEST(TaskDeclParsing, TaskDeclWithLifetimeAutomatic) {
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
}

TEST(TaskDeclParsing, TaskDeclWithLifetimeStatic) {
  auto r = Parse(
      "module m;\n"
      "  task static my_task;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->is_static);
  EXPECT_FALSE(item->is_automatic);
}

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

// --- task_body_declaration ---

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

TEST(TaskDeclParsing, TaskBodyOldStylePorts) {
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

TEST(TaskDeclParsing, TaskBodyWithEndLabel) {
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

TEST(TaskDeclParsing, TaskBodyClassScope) {
  auto r = Parse(
      "module m;\n"
      "  task MyClass::my_task;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->method_class, "MyClass");
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

// --- tf_item_declaration ---

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

// --- tf_port_list ---

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

TEST(TaskDeclParsing, TfPortListStickyDirection) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input int a, int b, output int c, int d);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 4u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[1].direction, Direction::kInput);
  EXPECT_EQ(item->func_args[2].direction, Direction::kOutput);
  EXPECT_EQ(item->func_args[3].direction, Direction::kOutput);
}

// --- tf_port_item ---

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
      "module m;\n"
      "  extern task my_task(input int);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_EQ(item->func_args[0].direction, Direction::kInput);
}

// --- tf_port_direction ---

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
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  task my_task(ref static int a);\n"
      "  endtask\n"
      "endmodule\n"));
}

// --- tf_port_declaration (old-style) ---

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

// --- task_prototype ---

TEST(TaskDeclParsing, TaskPrototypeWithArgs) {
  auto r = Parse(
      "module m;\n"
      "  extern task my_task(input int x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_extern);
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_TRUE(item->func_body_stmts.empty());
}

TEST(TaskDeclParsing, TaskPrototypeEmptyParens) {
  auto r = Parse(
      "module m;\n"
      "  extern task my_task();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->is_extern);
  EXPECT_TRUE(item->func_args.empty());
}

TEST(TaskDeclParsing, TaskPrototypeNoParens) {
  auto r = Parse(
      "module m;\n"
      "  extern task my_task;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->is_extern);
  EXPECT_TRUE(item->func_args.empty());
}

// --- dynamic_override_specifiers ---

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

// --- tf_port_direction: all directions in one task ---

TEST(TaskDeclParsing, TfPortAllDirections) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input int a, output int b, inout int c, ref int d);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  VerifyFuncArgDirections(r.cu->modules[0]->items[0],
                          {Direction::kInput, Direction::kOutput,
                           Direction::kInout, Direction::kRef});
}

}  // namespace
