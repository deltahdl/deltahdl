#include "fixture_parser.h"

using namespace delta;

namespace {

static ClassMember* FindMethodMember(ClassDecl* cls) {
  for (auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod) {
      return m;
    }
  }
  return nullptr;
}

// === class_declaration ===

TEST(ClassSyntaxParsing, EmptyClassDecl) {
  auto r = Parse("class Packet; endclass");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "Packet");
  EXPECT_TRUE(r.cu->classes[0]->members.empty());
}

TEST(ClassSyntaxParsing, ClassWithLifetime) {
  auto r = Parse(
      "class automatic MyClass;\n"
      "  int x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "MyClass");
}

TEST(ClassSyntaxParsing, EndLabelClass) {
  auto r = Parse("class myclass; endclass : myclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1);
  EXPECT_EQ(r.cu->classes[0]->name, "myclass");
}

TEST(ClassSyntaxParsing, VirtualClass) {
  auto r = Parse("virtual class base; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_virtual);
}

TEST(ClassSyntaxParsing, ClassWithExtends) {
  auto r = Parse(
      "class Derived extends Base;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->base_class, "Base");
}

TEST(ClassSyntaxParsing, ClassWithParameterPortList) {
  auto r = Parse(
      "class Param #(parameter int W = 8);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->params.size(), 1u);
}

TEST(ClassSyntaxParsing, InterfaceClassDecl) {
  auto r = Parse(
      "interface class iface_cls;\n"
      "  pure virtual function void do_work();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_interface);
}

TEST(ClassSyntaxParsing, InterfaceClassWithExtends) {
  auto r = Parse(
      "interface class Base; endclass\n"
      "interface class Derived extends Base;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_TRUE(r.cu->classes[1]->is_interface);
}

TEST(ClassSyntaxParsing, ImplementsSingleInterface) {
  auto r = Parse(
      "class C implements IFace;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->implements_types.size(), 1u);
  EXPECT_EQ(cls->implements_types[0], "IFace");
}

TEST(ClassSyntaxParsing, ExtendsWithArgs) {
  auto r = Parse(
      "class D extends Base(5);\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  EXPECT_EQ(cls->base_class, "Base");
  ASSERT_EQ(cls->extends_args.size(), 1u);
}

// === class_item ===

TEST(ClassSyntaxParsing, ClassEmptyItem) {
  auto r = Parse(
      "class C;\n"
      "  ;\n"
      "  int x;\n"
      "  ;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members.size(), 1u);
}

TEST(ClassSyntaxParsing, BasicClassWithProperty) {
  auto r = Parse(
      "module m;\n"
      "  class C;\n"
      "    int x;\n"
      "  endclass\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kClassDecl);
}

TEST(ClassSyntaxParsing, ClassParameters) {
  auto r = Parse(
      "class C;\n"
      "  localparam int LP = 10;\n"
      "  parameter int P = 20;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 2u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(members[1]->kind, ClassMemberKind::kProperty);
}

TEST(ClassSyntaxParsing, ParameterMemberInClass) {
  auto r = Parse(
      "class par_cls;\n"
      "  parameter int b = 23;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "par_cls");
}

TEST(ClassSyntaxParsing, LocalparamInClassItem) {
  EXPECT_TRUE(
      ParseOk("class my_class;\n"
              "  localparam int WIDTH = 8;\n"
              "endclass\n"));
}

TEST(ClassSyntaxParsing, CovergroupInClass) {
  EXPECT_TRUE(
      ParseOk("class my_class;\n"
              "  covergroup cg;\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "  int x;\n"
              "endclass\n"));
}

TEST(ClassSyntaxParsing, InterfaceClassItems) {
  auto r = Parse(
      "interface class IFace;\n"
      "  pure virtual function void do_work();\n"
      "  typedef int myint;\n"
      "  localparam int SIZE = 4;\n"
      "  parameter int W = 8;\n"
      "  ;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->classes[0]->is_interface);
}

// === class_property ===

TEST(ClassSyntaxParsing, ClassWithProperty) {
  auto r = Parse("class pkt; int data; endclass");
  ASSERT_NE(r.cu, nullptr);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->members.size(), 1);
  EXPECT_EQ(cls->members[0]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(cls->members[0]->name, "data");
  EXPECT_EQ(cls->members[0]->data_type.kind, DataTypeKind::kInt);
}

TEST(ClassSyntaxParsing, TwoPropertyDeclarations) {
  auto r = Parse(
      "class my_cls;\n"
      "  int data;\n"
      "  string name;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  EXPECT_EQ(cls->name, "my_cls");
  ASSERT_GE(cls->members.size(), 2u);
  EXPECT_EQ(cls->members[0]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(cls->members[0]->name, "data");
  EXPECT_EQ(cls->members[1]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(cls->members[1]->name, "name");
}

TEST(ClassSyntaxParsing, VariousPropertyDataTypes) {
  ParseOk(
      "class C;\n"
      "  int i;\n"
      "  real r;\n"
      "  string s;\n"
      "  bit [7:0] b;\n"
      "  logic [31:0] l;\n"
      "  byte by;\n"
      "  shortint si;\n"
      "  longint li;\n"
      "  integer ig;\n"
      "  time t;\n"
      "  chandle ch;\n"
      "  event e;\n"
      "endclass\n");
}

TEST(ClassSyntaxParsing, MultiplePropertiesCommaSeparated) {
  auto r = Parse(
      "class MyClass;\n"
      "  int a, b, c;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->members.size(), 3u);
  const std::string kExpectedNames[] = {"a", "b", "c"};
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(cls->members[i]->name, kExpectedNames[i]);
  }
}

TEST(ClassSyntaxParsing, ClassWithInitializer) {
  auto r = Parse(
      "class WithInit;\n"
      "  int x = 42;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 1u);
  EXPECT_NE(cls->members[0]->init_expr, nullptr);
}

TEST(ClassSyntaxParsing, PropertyWithUnpackedDimension) {
  auto r = Parse(
      "class C;\n"
      "  int data[4];\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_EQ(m->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(m->name, "data");
  EXPECT_FALSE(m->unpacked_dims.empty());
}

TEST(ClassSyntaxParsing, ClassPropertyWithAttr) {
  auto r = Parse(
      "class C;\n"
      "  (* my_attr *) int x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// === property_qualifier: random_qualifier ===

TEST(ClassSyntaxParsing, RandProperty) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->classes[0]->members[0]->is_rand);
}

TEST(ClassSyntaxParsing, RandcProperty) {
  auto r = Parse(
      "class C;\n"
      "  randc bit [2:0] x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->classes[0]->members[0]->is_randc);
}

// === property_qualifier: class_item_qualifier ===

TEST(ClassSyntaxParsing, StaticProperty) {
  auto r = Parse(
      "class C;\n"
      "  static int count;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->classes[0]->members[0]->is_static);
}

// === class_property: const variant ===

TEST(ClassSyntaxParsing, ConstPropertyVerifiesName) {
  auto r = Parse(
      "class MyClass;\n"
      "  const int MAX = 100;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 1u);
  EXPECT_TRUE(cls->members[0]->is_const);
  EXPECT_EQ(cls->members[0]->name, "MAX");
}

TEST(ClassSyntaxParsing, ConstAndStaticConstProperties) {
  auto r = Parse(
      "class C;\n"
      "  const int MAX = 100;\n"
      "  const static int SMAX = 200;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 2u);
  EXPECT_TRUE(members[0]->is_const);
  EXPECT_EQ(members[0]->name, "MAX");
  EXPECT_NE(members[0]->init_expr, nullptr);
  EXPECT_TRUE(members[1]->is_const);
  EXPECT_TRUE(members[1]->is_static);
}

TEST(ClassSyntaxParsing, ConstPropertyWithInitExpression) {
  auto r = Parse(
      "class Jumbo_Packet;\n"
      "  const int max_size = 9 * 1024;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_const);
  EXPECT_NE(m->init_expr, nullptr);
}

TEST(ClassSyntaxParsing, InstanceConstantNoInitializer) {
  auto r = Parse(
      "class Big_Packet;\n"
      "  const int size;\n"
      "  function new();\n"
      "    size = 4096;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_const);
  EXPECT_EQ(m->init_expr, nullptr);
}

TEST(ClassSyntaxParsing, StaticConstPropertyWithInitializer) {
  auto r = Parse(
      "class Config;\n"
      "  static const int VERSION = 3;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_static);
  EXPECT_TRUE(m->is_const);
  EXPECT_NE(m->init_expr, nullptr);
}

// === property_qualifier combinations ===

TEST(ClassSyntaxParsing, RandStaticProperty) {
  auto r = Parse(
      "class C;\n"
      "  static rand int count;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_rand);
  EXPECT_TRUE(m->is_static);
}

// === class_method ===

TEST(ClassSyntaxParsing, ClassWithMethod) {
  auto r = Parse(
      "class pkt;\n"
      "  function int get_data();\n"
      "    return data;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->members.size(), 1);
  EXPECT_EQ(cls->members[0]->kind, ClassMemberKind::kMethod);
  EXPECT_NE(cls->members[0]->method, nullptr);
}

TEST(ClassSyntaxParsing, ClassWithTask) {
  auto r = Parse(
      "class MyClass;\n"
      "  task do_stuff();\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* m = FindMethodMember(r.cu->classes[0]);
  ASSERT_NE(m, nullptr);
  ASSERT_NE(m->method, nullptr);
  EXPECT_EQ(m->method->kind, ModuleItemKind::kTaskDecl);
}

TEST(ClassSyntaxParsing, ClassMethods) {
  auto r = Parse(
      "class C;\n"
      "  function void foo(); endfunction\n"
      "  task bar(); endtask\n"
      "  static function int sfn(); endfunction\n"
      "  virtual task vtask(); endtask\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 4u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(members[0]->method->name, "foo");
  EXPECT_EQ(members[1]->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(members[1]->method->name, "bar");
  EXPECT_TRUE(members[2]->is_static);
  EXPECT_TRUE(members[3]->is_virtual);
}

TEST(ClassSyntaxParsing, ClassMethodsAndProperties) {
  auto r = Parse(
      "class my_cls;\n"
      "  int count;\n"
      "  function void increment();\n"
      "    count = count + 1;\n"
      "  endfunction\n"
      "  task reset();\n"
      "    count = 0;\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 3u);
  EXPECT_EQ(cls->members[0]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(cls->members[0]->name, "count");
  EXPECT_EQ(cls->members[1]->kind, ClassMemberKind::kMethod);
  ASSERT_NE(cls->members[1]->method, nullptr);
  EXPECT_EQ(cls->members[1]->method->name, "increment");
  EXPECT_EQ(cls->members[2]->kind, ClassMemberKind::kMethod);
  ASSERT_NE(cls->members[2]->method, nullptr);
  EXPECT_EQ(cls->members[2]->method->name, "reset");
}

TEST(ClassSyntaxParsing, MethodWithAttribute) {
  auto r = Parse(
      "class C;\n"
      "  (* my_attr *) function void work();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->classes[0]->members[0]->kind, ClassMemberKind::kMethod);
}

// === method_qualifier: virtual ===

TEST(ClassSyntaxParsing, VirtualMethod) {
  auto r = Parse(
      "class C;\n"
      "  virtual function void display();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->classes[0]->members[0]->is_virtual);
}

TEST(ClassSyntaxParsing, ClassWithVirtualMethod) {
  auto r = Parse(
      "class Base;\n"
      "  virtual function void display();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  bool found = false;
  for (auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->is_virtual) {
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ClassSyntaxParsing, PureVirtualMethod) {
  auto r = Parse(
      "class C;\n"
      "  pure virtual function void work();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_virtual);
}

TEST(ClassSyntaxParsing, PureVirtualTaskPrototype) {
  auto r = Parse(
      "class C;\n"
      "  pure virtual task run();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_EQ(m->kind, ClassMemberKind::kMethod);
  EXPECT_TRUE(m->is_virtual);
}

// === method_qualifier: class_item_qualifier ===

TEST(ClassSyntaxParsing, MixedStaticFuncAndTask) {
  auto r = Parse(
      "virtual class Utils#(parameter N = 4);\n"
      "  static function int max_val();\n"
      "    return (1 << N) - 1;\n"
      "  endfunction\n"
      "  static task report();\n"
      "    $display(\"N=%0d\", N);\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes[0]->members.size(), 2u);
}

TEST(ClassSyntaxParsing, StaticMethodNoArgs) {
  auto r = Parse(
      "virtual class Constants#(parameter N = 32);\n"
      "  static function int zero();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ClassSyntaxParsing, StaticMethodMultipleArgs) {
  EXPECT_TRUE(
      ParseOk("virtual class Arith#(parameter W = 16);\n"
              "  static function logic [W-1:0] add(\n"
              "      input logic [W-1:0] a,\n"
              "      input logic [W-1:0] b);\n"
              "    return a + b;\n"
              "  endfunction\n"
              "endclass\n"));
}

// === class_method: extern ===

TEST(ClassSyntaxParsing, ExternMethod) {
  auto r = Parse(
      "class C;\n"
      "  extern function void compute();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassSyntaxParsing, ExternVirtualMethodPrototype) {
  auto r = Parse(
      "class C;\n"
      "  extern virtual function void compute();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->method->is_extern);
  EXPECT_TRUE(m->is_virtual);
}

TEST(ClassSyntaxParsing, ClassMethodPrototype) {
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

TEST(ClassSyntaxParsing, ExternConstructorPrototype) {
  auto r = Parse(
      "class C;\n"
      "  extern function new(int x);\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 1u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(members[0]->method->name, "new");
}

// === dynamic_override_specifiers ===

TEST(ClassSyntaxParsing, MethodInitialSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  function :initial void foo(); endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
}

TEST(ClassSyntaxParsing, MethodExtendsSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  function :extends void bar(); endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
}

TEST(ClassSyntaxParsing, MethodFinalSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  function :final void baz(); endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
}

TEST(ClassSyntaxParsing, MethodInitialFinalSpecifiers) {
  auto r = Parse(
      "class C;\n"
      "  function :initial :final void qux(); endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
}

TEST(ClassSyntaxParsing, TaskExtendsSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  task :extends my_task(); endtask\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
}

TEST(ClassSyntaxParsing, VirtualFunctionInitialSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :initial int foo(); return 0; endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassSyntaxParsing, VirtualFunctionExtendsSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :extends int foo(); return 0; endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassSyntaxParsing, VirtualFunctionFinalSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :final int foo(); return 0; endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassSyntaxParsing, VirtualFunctionInitialFinalSpecifiers) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :initial :final int foo();\n"
      "    return 0;\n  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassSyntaxParsing, VirtualFunctionExtendsFinalSpecifiers) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :extends :final int foo();\n"
      "    return 0;\n  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassSyntaxParsing, VirtualTaskInitialSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :initial my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassSyntaxParsing, VirtualTaskExtendsSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :extends my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassSyntaxParsing, VirtualTaskFinalSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :final my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassSyntaxParsing, VirtualTaskInitialFinalSpecifiers) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :initial :final my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassSyntaxParsing, VirtualTaskExtendsFinalSpecifiers) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :extends :final my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassSyntaxParsing, InitialSpecifierStored) {
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

TEST(ClassSyntaxParsing, ExtendsSpecifierStored) {
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

TEST(ClassSyntaxParsing, FinalSpecifierStored) {
  auto r = Parse(
      "class C;\n"
      "  virtual function :final int foo(); return 0; endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* m = r.cu->classes[0]->members[0]->method;
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_method_final);
}

TEST(ClassSyntaxParsing, InitialFinalCombined) {
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

TEST(ClassSyntaxParsing, ExtendsFinalCombined) {
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

TEST(ClassSyntaxParsing, TaskInitialSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  virtual task :initial my_task(); endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* m = r.cu->classes[0]->members[0]->method;
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_method_initial);
}

// === class_constructor_declaration ===

TEST(ClassSyntaxParsing, ClassConstructor) {
  auto r = Parse(
      "class Packet;\n"
      "  int data;\n"
      "  function new();\n"
      "    data = 0;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* m = FindMethodMember(r.cu->classes[0]);
  ASSERT_NE(m, nullptr);
  ASSERT_NE(m->method, nullptr);
  EXPECT_EQ(m->method->name, "new");
}

TEST(ClassSyntaxParsing, ClassConstructorDecl) {
  auto r = Parse(
      "class C;\n"
      "  function new(int val);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 1u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(members[0]->method->name, "new");
}

TEST(ClassSyntaxParsing, SimpleConstructorDeclaration) {
  auto r = Parse(
      "class C;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassSyntaxParsing, ConstructorNoParens) {
  auto r = Parse(
      "class C;\n"
      "  function new;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 1u);
  EXPECT_EQ(members[0]->method->name, "new");
}

TEST(ClassSyntaxParsing, ConstructorDeclarationWithEndLabel) {
  auto r = Parse(
      "class C;\n"
      "  function new(int x);\n"
      "  endfunction : new\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassSyntaxParsing, ConstructorDefaultArgs) {
  auto r = Parse(
      "class Packet;\n"
      "  int command;\n"
      "  int address;\n"
      "  function new(int cmd = 0, bit [12:0] adrs = 0);\n"
      "    command = cmd;\n"
      "    address = adrs;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* cls = r.cu->classes[0];
  auto* m = FindMethodMember(cls);
  ASSERT_NE(m, nullptr);
  EXPECT_EQ(m->method->name, "new");
  ASSERT_GE(m->method->func_args.size(), 2u);
  EXPECT_NE(m->method->func_args[0].default_value, nullptr);
  EXPECT_NE(m->method->func_args[1].default_value, nullptr);
}

TEST(ClassSyntaxParsing, ClassNewWithDefaultArg) {
  EXPECT_TRUE(
      ParseOk("class my_class;\n"
              "  int x;\n"
              "  function new(int a = 0);\n"
              "    x = a;\n"
              "  endfunction\n"
              "endclass\n"));
}

TEST(ClassSyntaxParsing, ExternConstructorPrototypeNoArgs) {
  auto r = Parse(
      "class C;\n"
      "  extern function new;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 1u);
  EXPECT_EQ(members[0]->method->name, "new");
}

// === class_constraint ===

TEST(ClassSyntaxParsing, ConstraintPrototype) {
  auto r = Parse(
      "class C;\n"
      "  constraint valid_range;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassSyntaxParsing, ConstraintDeclaration) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c_x { x > 0; x < 100; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// === class_item: nested class_declaration / interface_class_declaration ===

TEST(ClassSyntaxParsing, ClassNestedClass) {
  auto r = Parse(
      "class Outer;\n"
      "  class Inner;\n"
      "    int val;\n"
      "  endclass\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 1u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kClassDecl);
  EXPECT_EQ(members[0]->nested_class->name, "Inner");
}

TEST(ClassSyntaxParsing, NestedClassWithInstance) {
  auto r = Parse(
      "class Outer;\n"
      "  class Inner;\n"
      "    int x;\n"
      "  endclass\n"
      "  Inner inst;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "Outer");
}

TEST(ClassSyntaxParsing, NestedInterfaceClassDeclaration) {
  auto r = Parse(
      "class Outer;\n"
      "  interface class Inner;\n"
      "    pure virtual function void work();\n"
      "  endclass\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassSyntaxParsing, ClassWithTypedef) {
  auto r = Parse(
      "class test_cls;\n"
      "  typedef enum {A = 10, B = 20} e_type;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "test_cls");
}

TEST(ClassSyntaxParsing, ClassCovergroup) {
  auto r = Parse(
      "class C;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassSyntaxParsing, InterfaceMethodDefaultArgs) {
  EXPECT_TRUE(
      ParseOk("interface class IC;\n"
              "  pure virtual function void foo(int a = 5);\n"
              "endclass\n"));
}

TEST(ClassSyntaxParsing, InterfaceMethodMultipleDefaultArgs) {
  EXPECT_TRUE(
      ParseOk("interface class IC;\n"
              "  pure virtual function int calc(int a = 0, int b = 1);\n"
              "endclass\n"));
}

TEST(ClassSyntaxParsing, InterfaceClassPureVirtualTask) {
  ParseOk(
      "interface class IC;\n"
      "  pure virtual task run();\n"
      "endclass\n");
}

// === Footnote 10: mutual exclusivity ===

TEST(ClassSyntaxParsing, ErrorDuplicateStatic) {
  auto r = Parse(
      "class C;\n"
      "  static static int x;\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ClassSyntaxParsing, ErrorRandAndRandc) {
  auto r = Parse(
      "class C;\n"
      "  rand randc int x;\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ClassSyntaxParsing, ErrorDuplicateRand) {
  auto r = Parse(
      "class C;\n"
      "  rand rand int x;\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ClassSyntaxParsing, ErrorDuplicateRandc) {
  auto r = Parse(
      "class C;\n"
      "  randc randc bit [2:0] x;\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

// === class_declaration: implements multiple interfaces ===

TEST(ClassSyntaxParsing, ImplementsMultipleInterfaces) {
  auto r = Parse(
      "interface class IA; endclass\n"
      "interface class IB; endclass\n"
      "interface class IC; endclass\n"
      "class C implements IA, IB, IC;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* cls = r.cu->classes[3];
  ASSERT_EQ(cls->implements_types.size(), 3u);
  EXPECT_EQ(cls->implements_types[0], "IA");
  EXPECT_EQ(cls->implements_types[1], "IB");
  EXPECT_EQ(cls->implements_types[2], "IC");
}

// === class_declaration: extends + implements combined ===

TEST(ClassSyntaxParsing, ExtendsAndImplementsCombined) {
  auto r = Parse(
      "interface class IA; endclass\n"
      "class Base; endclass\n"
      "class C extends Base implements IA;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* cls = r.cu->classes[2];
  EXPECT_EQ(cls->base_class, "Base");
  ASSERT_EQ(cls->implements_types.size(), 1u);
  EXPECT_EQ(cls->implements_types[0], "IA");
}

// === class_declaration: virtual + final combined ===

TEST(ClassSyntaxParsing, VirtualFinalClass) {
  auto r = Parse("virtual class :final C; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_virtual);
  EXPECT_TRUE(r.cu->classes[0]->is_final);
}

// === class_method: extern with method_qualifier combinations ===

TEST(ClassSyntaxParsing, ExternStaticMethodPrototype) {
  auto r = Parse(
      "class C;\n"
      "  extern static function void compute();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_static);
  EXPECT_TRUE(m->method->is_extern);
}

// === class_constructor_prototype: multiple args, default ===

TEST(ClassSyntaxParsing, ExternConstructorPrototypeMultipleArgs) {
  auto r = Parse(
      "class C;\n"
      "  extern function new(int a, string b);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_EQ(m->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(m->method->name, "new");
  EXPECT_TRUE(m->method->is_extern);
}

TEST(ClassSyntaxParsing, ExternConstructorPrototypeWithDefault) {
  auto r = Parse(
      "class C;\n"
      "  extern function new(int a, default);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// === class_constraint: with dynamic_override_specifiers ===

TEST(ClassSyntaxParsing, ConstraintWithInitialSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  constraint :initial my_c { x > 0; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->classes[0]->members[0]->kind, ClassMemberKind::kConstraint);
}

TEST(ClassSyntaxParsing, ConstraintWithFinalSpecifier) {
  auto r = Parse(
      "class C;\n"
      "  constraint :final my_c { x > 0; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->classes[0]->members[0]->kind, ClassMemberKind::kConstraint);
}

TEST(ClassSyntaxParsing, ConstraintWithExtendsFinalSpecifiers) {
  auto r = Parse(
      "class C;\n"
      "  constraint :extends :final my_c { x > 0; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->classes[0]->members[0]->kind, ClassMemberKind::kConstraint);
}

// === class_constraint: pure and extern prototypes ===

TEST(ClassSyntaxParsing, PureConstraintPrototype) {
  auto r = Parse(
      "class C;\n"
      "  pure constraint my_c;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->classes[0]->members[0]->kind, ClassMemberKind::kConstraint);
}

TEST(ClassSyntaxParsing, ExternConstraintPrototype) {
  auto r = Parse(
      "class C;\n"
      "  extern constraint my_c;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->classes[0]->members[0]->kind, ClassMemberKind::kConstraint);
}

TEST(ClassSyntaxParsing, StaticConstraintDeclaration) {
  auto r = Parse(
      "class C;\n"
      "  static constraint my_c { x > 0; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->classes[0]->members[0]->kind, ClassMemberKind::kConstraint);
}

}  // namespace
