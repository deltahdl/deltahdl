#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// §8.24: Class with extern method prototype + out-of-block body in module.
TEST(ParserSection8, OutOfBlockMethod) {
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

// §8.24: Module-level extern function declaration.
TEST(ParserA26, FuncPrototypeExtern) {
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

// §8.24: Class method prototypes with extern.
TEST(SourceText, ClassMethodPrototype) {
  auto r = Parse(
      "class C;\n"
      "  extern function int get_val();\n"
      "  extern task do_work();\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 2u);
  EXPECT_EQ(members[0]->method->name, "get_val");
  EXPECT_TRUE(members[0]->method->is_extern);
  EXPECT_EQ(members[1]->method->name, "do_work");
  EXPECT_TRUE(members[1]->method->is_extern);
}

// §8.24: Out-of-block function stores method_class.
TEST(ParserA26, FuncBodyClassScope) {
  auto r = Parse(
      "class C;\n"
      "  extern function int foo();\n"
      "endclass\n"
      "function int C::foo();\n"
      "  return 42;\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // The CU-level function should have method_class set.
  ASSERT_GE(r.cu->modules.size() + r.cu->classes.size(), 1u);
}

// §8.24: Out-of-block function — method_class field set to "C".
TEST(ParserSection8_24, FuncBodyMethodClassStored) {
  auto r = Parse(
      "class C;\n"
      "  extern function int foo();\n"
      "endclass\n"
      "function int C::foo();\n"
      "  return 42;\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // Find the out-of-block function in CU-level items.
  bool found = false;
  for (auto* item : r.cu->cu_items) {
    if (item->kind == ModuleItemKind::kFunctionDecl && item->name == "foo") {
      EXPECT_EQ(item->method_class, "C");
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

// §8.24: Out-of-block constructor stores method_class.
TEST(ParserA26, FuncBodyOutOfBlockConstructor) {
  auto r = Parse(
      "class C;\n"
      "  extern function new();\n"
      "endclass\n"
      "function C::new();\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §8.24: Out-of-block task stores method_class.
TEST(ParserA27, TaskBodyClassScope) {
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

// §8.24: Out-of-block task — method_class field set.
TEST(ParserSection8_24, TaskBodyMethodClassStored) {
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

// §8.24: Non-out-of-block function has empty method_class.
TEST(ParserSection8_24, RegularFuncNoMethodClass) {
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
