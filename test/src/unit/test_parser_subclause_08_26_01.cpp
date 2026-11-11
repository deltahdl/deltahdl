#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_class.h"

using namespace delta;

namespace {

TEST(InterfaceClassSyntax, InterfaceClassItems) {
  auto r = Parse(
      "interface class IC;\n"
      "  pure virtual function void do_thing();\n"
      "  pure virtual task do_task();\n"
      "  typedef int my_int;\n"
      "  localparam int LP = 5;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_interface);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 4u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kMethod);
  EXPECT_TRUE(members[0]->is_virtual);
  EXPECT_EQ(members[1]->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(members[2]->kind, ClassMemberKind::kTypedef);
  EXPECT_EQ(members[3]->kind, ClassMemberKind::kProperty);
}

TEST(InterfaceClassSyntax, ClassNestedInterfaceClass) {
  auto r = Parse(
      "class Outer;\n"
      "  interface class IFace;\n"
      "    pure virtual function void do_it();\n"
      "  endclass\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 1u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kClassDecl);
  EXPECT_TRUE(members[0]->nested_class->is_interface);
}

TEST(InterfaceClassSyntax, InterfaceClassExtendsMultiple) {
  auto r = Parse(
      "interface class IFace extends IBase1, IBase2;\n"
      "  pure virtual function void do_something();\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_interface);
  EXPECT_EQ(r.cu->classes[0]->base_class, "IBase1");
  ASSERT_EQ(r.cu->classes[0]->extends_interfaces.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->extends_interfaces[0].name, "IBase2");
}

TEST(InterfaceClassSyntax, InterfaceClassItemsAllAlternatives) {
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

TEST(InterfaceClassSyntax, EndclassLabel) {
  auto r = Parse(
      "interface class IC;\n"
      "  pure virtual function void f();\n"
      "endclass : IC\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "IC");
  EXPECT_TRUE(r.cu->classes[0]->is_interface);
}

TEST(InterfaceClassSyntax, ParameterPortList) {
  auto r = Parse(
      "interface class IC #(type T = logic, int W = 8);\n"
      "  pure virtual function T get();\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_interface);
  EXPECT_EQ(r.cu->classes[0]->params.size(), 2u);
}

TEST(InterfaceClassSyntax, ExtendsWithTypeParams) {
  auto r = Parse(
      "interface class IBase; endclass\n"
      "interface class IDerived extends IBase#(int);\n"
      "  pure virtual function void work();\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_TRUE(r.cu->classes[1]->is_interface);
  EXPECT_EQ(r.cu->classes[1]->base_class, "IBase");
}

TEST(InterfaceClassSyntax, AttributeOnMethod) {
  auto r = Parse(
      "interface class IC;\n"
      "  (* synthesis_off *) pure virtual function void f();\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_interface);
  ASSERT_EQ(r.cu->classes[0]->members.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members[0]->kind, ClassMemberKind::kMethod);
}

TEST(InterfaceClassSyntax, ParameterBodyItemNotInPortList) {
  auto r = Parse(
      "interface class IC;\n"
      "  parameter int WIDTH = 8;\n"
      "  pure virtual function void f();\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->params.empty());
}

TEST(InterfaceClassSyntax, EmptyInterfaceClass) {
  auto r = Parse("interface class IC; endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "IC");
  EXPECT_TRUE(r.cu->classes[0]->is_interface);
  EXPECT_TRUE(r.cu->classes[0]->members.empty());
}

TEST(InterfaceClassSyntax, ExtendsThreeBases) {
  auto r = Parse(
      "interface class IC extends IA, IB, ICBase;\n"
      "  pure virtual function void f();\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->base_class, "IA");
  ASSERT_EQ(r.cu->classes[0]->extends_interfaces.size(), 2u);
  EXPECT_EQ(r.cu->classes[0]->extends_interfaces[0].name, "IB");
  EXPECT_EQ(r.cu->classes[0]->extends_interfaces[1].name, "ICBase");
}

TEST(InterfaceClassSyntax, SingleExtendsNoAdditionalBases) {
  auto r = Parse(
      "interface class IC extends IBase;\n"
      "  pure virtual function void f();\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->classes[0]->base_class, "IBase");
  EXPECT_TRUE(r.cu->classes[0]->extends_interfaces.empty());
}

TEST(InterfaceClassSyntax, PureVirtualMethodWithFormalArgs) {
  auto r = Parse(
      "interface class IC;\n"
      "  pure virtual function void put(int a);\n"
      "  pure virtual task run(int a, bit b);\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_interface);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 2u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kMethod);
  EXPECT_TRUE(members[0]->is_pure_virtual);
  ASSERT_NE(members[0]->method, nullptr);
  EXPECT_EQ(members[0]->method->func_args.size(), 1u);
  EXPECT_EQ(members[1]->kind, ClassMemberKind::kMethod);
  EXPECT_TRUE(members[1]->is_pure_virtual);
  ASSERT_NE(members[1]->method, nullptr);
  EXPECT_EQ(members[1]->method->func_args.size(), 2u);
}

TEST(InterfaceClassSyntax, SecondExtendsBaseWithTypeParams) {
  auto r = Parse(
      "interface class IA; endclass\n"
      "interface class IB; endclass\n"
      "interface class IC extends IA, IB#(int);\n"
      "  pure virtual function void f();\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 3u);
  EXPECT_EQ(r.cu->classes[2]->base_class, "IA");
  ASSERT_EQ(r.cu->classes[2]->extends_interfaces.size(), 1u);
  EXPECT_EQ(r.cu->classes[2]->extends_interfaces[0].name, "IB");
}

TEST(InterfaceClassParsing, ExternPrototypeAndAMismatchedEndLabelAreRefused) {
  auto r = Parse(
      "interface class I1;\n"
      "  int x;\n"
      "endclass\n"
      "interface class I2;\n"
      "  function void f(); endfunction\n"
      "endclass\n"
      "interface class I3;\n"
      "  virtual function void f(); endfunction\n"
      "endclass\n"
      "interface class I4;\n"
      "  constraint c { 1; }\n"
      "endclass\n"
      "interface class I5;\n"
      "  covergroup cg; endgroup\n"
      "endclass\n"
      "interface class I6;\n"
      "  class N; endclass\n"
      "endclass\n"
      "interface class I7;\n"
      "  interface class NI; endclass\n"
      "endclass\n"
      "interface class I8;\n"
      "  static function void f(); endfunction\n"
      "endclass\n"
      "interface class I9;\n"
      "  task t(); endtask\n"
      "endclass\n"
      "interface class I10;\n"
      "  rand int r;\n"
      "endclass\n"
      "interface class I11;\n"
      "  extern virtual function void f();\n"
      "endclass\n"
      "interface class OK;\n"
      "  typedef int t_t;\n"
      "  parameter int P = 1;\n"
      "  localparam int L = 2;\n"
      "  pure virtual function void f();\n"
      "  pure virtual task t();\n"
      "  ;\n"
      "  (* a *) pure virtual function int g(int a = 3);\n"
      "endclass : OK\n"
      "class Holder;\n"
      "  interface class HI; pure virtual function void f(); endclass\n"
      "endclass\n"
      "package pk;\n"
      "  interface class PI; pure virtual function void f(); endclass\n"
      "endpackage\n"
      "module m;\n"
      "  interface class MI; pure virtual function void f(); endclass\n"
      "endmodule\n"
      "interface ifc;\n"
      "  interface class FI; pure virtual function void f(); endclass\n"
      "endinterface\n"
      "program prg;\n"
      "  interface class GI; pure virtual function void f(); endclass\n"
      "endprogram\n"
      "interface class I12;\n"
      "  enum {A, B} e;\n"
      "endclass\n"
      "interface class I13 #(int Q = 1);\n"
      "  pure virtual function void f();\n"
      "endclass : I13x\n");
  const auto& diags = r.diags;
  EXPECT_TRUE(ReportedError(
      diags, "'extern' is no qualifier of a method of an interface class", 32,
      "A.1.9"));
  EXPECT_TRUE(ReportedError(diags, "end label 'I13x' does not match 'I13'", 63,
                            "9.3.4"));
}

}  // namespace
