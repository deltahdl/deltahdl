#include "fixture_parser.h"

using namespace delta;
namespace {

TEST(ClassParsing, OutOfBlockMethod) {
  auto r = Parse(
      "module m;\n"
      "  class test_cls;\n"
      "    int a;\n"
      "    extern function void test_method(int val);\n"
      "  endclass\n"
      "  function void test_cls::test_method(int val);\n"
      "    a = val;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(FunctionDeclParsing, FuncPrototypeExtern) {
  auto r = Parse(
      "module m;\n"
      "  extern function int foo(input int x);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->is_extern);
  EXPECT_EQ(item->name, "foo");
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInt);
}

TEST(FunctionDeclParsing, FuncBodyClassScope) {
  auto r = Parse(
      "class C;\n"
      "  extern function int foo();\n"
      "endclass\n"
      "function int C::foo();\n"
      "  return 42;\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  ASSERT_GE(r.cu->modules.size() + r.cu->classes.size(), 1u);
}

TEST(ParameterizedClassParsing, FuncBodyMethodClassStored) {
  auto r = Parse(
      "class C;\n"
      "  extern function int foo();\n"
      "endclass\n"
      "function int C::foo();\n"
      "  return 42;\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  bool found = false;
  for (auto* item : r.cu->cu_items) {
    if (item->kind == ModuleItemKind::kFunctionDecl && item->name == "foo") {
      EXPECT_EQ(item->method_class, "C");
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(FunctionDeclParsing, FuncBodyOutOfBlockConstructor) {
  auto r = Parse(
      "class C;\n"
      "  extern function new();\n"
      "endclass\n"
      "function C::new();\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(TaskDeclParsing, TaskBodyClassScope) {
  auto r = Parse(
      "class C;\n"
      "  extern task my_task(input int x);\n"
      "endclass\n"
      "task C::my_task(input int x);\n"
      "  $display(\"x=%0d\", x);\n"
      "endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParameterizedClassParsing, TaskBodyMethodClassStored) {
  auto r = Parse(
      "class C;\n"
      "  extern task run();\n"
      "endclass\n"
      "task C::run();\n"
      "endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->cu_items) {
    if (item->kind == ModuleItemKind::kTaskDecl && item->name == "run") {
      EXPECT_EQ(item->method_class, "C");
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ParameterizedClassParsing, RegularFuncNoMethodClass) {
  auto r = Parse(
      "function int bar();\n"
      "  return 0;\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto* item : r.cu->cu_items) {
    if (item->kind == ModuleItemKind::kFunctionDecl && item->name == "bar") {
      EXPECT_TRUE(item->method_class.empty());
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
