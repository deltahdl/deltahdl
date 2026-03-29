#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(VirtualMethodParsing, DerivedOverrideWithoutVirtual) {
  EXPECT_TRUE(
      ParseOk("class Base;\n"
              "  virtual function void display(); endfunction\n"
              "endclass\n"
              "class Derived extends Base;\n"
              "  function void display(); endfunction\n"
              "endclass\n"));
}

// === dynamic_override_specifiers ===

TEST(VirtualMethodParsing, MethodInitialSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  function :initial void foo(); endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
}

TEST(VirtualMethodParsing, MethodExtendsSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  function :extends void bar(); endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
}

TEST(VirtualMethodParsing, MethodFinalSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  function :final void baz(); endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
}

TEST(VirtualMethodParsing, MethodInitialFinalSpecifiers) {
  auto r = Parse(
      "class C;\n"
      "  function :initial :final void qux(); endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
}

TEST(VirtualMethodParsing, TaskExtendsSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  task :extends my_task(); endtask\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
}

TEST(VirtualMethodParsing, VirtualFunctionInitialSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :initial int foo(); return 0; endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(VirtualMethodParsing, VirtualFunctionExtendsSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :extends int foo(); return 0; endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(VirtualMethodParsing, VirtualFunctionFinalSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :final int foo(); return 0; endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(VirtualMethodParsing, VirtualFunctionInitialFinalSpecifiers) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :initial :final int foo();\n"
      "    return 0;\n  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(VirtualMethodParsing, VirtualFunctionExtendsFinalSpecifiers) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :extends :final int foo();\n"
      "    return 0;\n  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(VirtualMethodParsing, VirtualTaskInitialSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :initial my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(VirtualMethodParsing, VirtualTaskExtendsSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :extends my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(VirtualMethodParsing, VirtualTaskFinalSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :final my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(VirtualMethodParsing, VirtualTaskInitialFinalSpecifiers) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :initial :final my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(VirtualMethodParsing, VirtualTaskExtendsFinalSpecifiers) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :extends :final my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(VirtualMethodParsing, InitialSpecifierStored) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :initial int foo(); return 0; endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* m = r.cu->classes[0]->members[0]->method;
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_method_initial);
  EXPECT_FALSE(m->is_method_extends);
  EXPECT_FALSE(m->is_method_final);
}

TEST(VirtualMethodParsing, ExtendsSpecifierStored) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :extends int foo(); return 0; endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* m = r.cu->classes[0]->members[0]->method;
  ASSERT_NE(m, nullptr);
  EXPECT_FALSE(m->is_method_initial);
  EXPECT_TRUE(m->is_method_extends);
}

TEST(VirtualMethodParsing, FinalSpecifierStored) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :final int foo(); return 0; endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* m = r.cu->classes[0]->members[0]->method;
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_method_final);
}

TEST(VirtualMethodParsing, InitialFinalCombined) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :initial :final int foo();\n"
      "    return 0;\n  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* m = r.cu->classes[0]->members[0]->method;
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_method_initial);
  EXPECT_TRUE(m->is_method_final);
}

TEST(VirtualMethodParsing, ExtendsFinalCombined) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :extends :final int foo();\n"
      "    return 0;\n  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* m = r.cu->classes[0]->members[0]->method;
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_method_extends);
  EXPECT_TRUE(m->is_method_final);
}

TEST(VirtualMethodParsing, TaskInitialSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :initial my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* m = r.cu->classes[0]->members[0]->method;
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_method_initial);
}

}  // namespace
