#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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

TEST(InterfaceClassSyntax, InterfaceClassDecl) {
  auto r = Parse("interface class IC; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "IC");
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
  EXPECT_EQ(r.cu->classes[0]->extends_interfaces[0], "IBase2");
}

TEST(InterfaceClassSyntax, InterfaceClassWithExtends) {
  auto r = Parse(
      "interface class Base; endclass\n"
      "interface class Derived extends Base;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_TRUE(r.cu->classes[1]->is_interface);
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

TEST(InterfaceClassSyntax, InterfaceClassPureVirtualTask) {
  ParseOk(
      "interface class IC;\n"
      "  pure virtual task run();\n"
      "endclass\n");
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
  EXPECT_EQ(r.cu->classes[0]->extends_interfaces[0], "IB");
  EXPECT_EQ(r.cu->classes[0]->extends_interfaces[1], "ICBase");
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

}  // namespace
