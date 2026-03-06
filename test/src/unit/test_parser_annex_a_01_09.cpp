#include "fixture_parser.h"

using namespace delta;

namespace {

// §A.1.9 Class items

// class_item ::= { attribute_instance } class_property
TEST(ClassItemsA19, ClassProperty) {
  auto r = Parse(
      "class C;\n"
      "  int x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ASSERT_GE(r.cu->classes[0]->members.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members[0]->kind, ClassMemberKind::kProperty);
}

// class_property ::= { property_qualifier } data_declaration
TEST(ClassItemsA19, RandProperty) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->classes[0]->members[0]->is_rand);
}

TEST(ClassItemsA19, RandcProperty) {
  auto r = Parse(
      "class C;\n"
      "  randc bit [2:0] x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->classes[0]->members[0]->is_randc);
}

TEST(ClassItemsA19, StaticProperty) {
  auto r = Parse(
      "class C;\n"
      "  static int count;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->classes[0]->members[0]->is_static);
}

TEST(ClassItemsA19, ProtectedProperty) {
  auto r = Parse(
      "class C;\n"
      "  protected int data;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->classes[0]->members[0]->is_protected);
}

TEST(ClassItemsA19, LocalProperty) {
  auto r = Parse(
      "class C;\n"
      "  local int secret;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->classes[0]->members[0]->is_local);
}

// class_property ::= const { class_item_qualifier } data_type const_id
//                    [ = constant_expression ] ;
TEST(ClassItemsA19, ConstProperty) {
  auto r = Parse(
      "class C;\n"
      "  const int MAX = 100;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->classes[0]->members[0]->is_const);
}

// class_item ::= { attribute_instance } class_method
TEST(ClassItemsA19, ClassMethodFunction) {
  auto r = Parse(
      "class C;\n"
      "  function void work();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_EQ(m->kind, ClassMemberKind::kMethod);
}

TEST(ClassItemsA19, ClassMethodTask) {
  auto r = Parse(
      "class C;\n"
      "  task run();\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_EQ(m->kind, ClassMemberKind::kMethod);
}

// class_method ::= pure virtual { class_item_qualifier } method_prototype ;
TEST(ClassItemsA19, PureVirtualMethod) {
  auto r = Parse(
      "class C;\n"
      "  pure virtual function void work();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_virtual);
}

// class_method ::= extern { method_qualifier } method_prototype ;
TEST(ClassItemsA19, ExternMethod) {
  auto r = Parse(
      "class C;\n"
      "  extern function void compute();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// class_method ::= virtual method
TEST(ClassItemsA19, VirtualMethod) {
  auto r = Parse(
      "class C;\n"
      "  virtual function void display();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->classes[0]->members[0]->is_virtual);
}

// class_method ::= static method
TEST(ClassItemsA19, StaticMethod) {
  auto r = Parse(
      "class C;\n"
      "  static function int get_count();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->classes[0]->members[0]->is_static);
}

// class_method ::= class_constructor_declaration
TEST(ClassItemsA19, Constructor) {
  auto r = Parse(
      "class C;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassItemsA19, ConstructorWithArgs) {
  auto r = Parse(
      "class C;\n"
      "  function new(int val);\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// class_item ::= class_constraint (constraint_prototype)
TEST(ClassItemsA19, ConstraintPrototype) {
  auto r = Parse(
      "class C;\n"
      "  constraint valid_range;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// class_item ::= class_constraint (constraint_declaration)
TEST(ClassItemsA19, ConstraintDeclaration) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c_x { x > 0; x < 100; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// class_item ::= class_declaration (nested)
TEST(ClassItemsA19, NestedClass) {
  auto r = Parse(
      "class Outer;\n"
      "  class Inner;\n"
      "    int x;\n"
      "  endclass\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// class_item ::= covergroup_declaration
TEST(ClassItemsA19, ClassCovergroup) {
  auto r = Parse(
      "class C;\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// class_item ::= local_parameter_declaration ;
TEST(ClassItemsA19, ClassLocalparam) {
  auto r = Parse(
      "class C;\n"
      "  localparam int MAX = 255;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// class_item ::= parameter_declaration ;
TEST(ClassItemsA19, ClassParameter) {
  auto r = Parse(
      "class C;\n"
      "  parameter int W = 8;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// class_item ::= ;  (null item)
TEST(ClassItemsA19, ClassNullItem) {
  auto r = Parse(
      "class C;\n"
      "  ;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// class with attributes on members
TEST(ClassItemsA19, ClassPropertyWithAttr) {
  auto r = Parse(
      "class C;\n"
      "  (* my_attr *) int x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// interface_class_declaration items
TEST(ClassItemsA19, InterfaceClassItems) {
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

// class_declaration with extends and arg list
TEST(ClassItemsA19, ClassExtendsWithArgs) {
  auto r = Parse(
      "class Derived extends Base(1, 2);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// class with end label
TEST(ClassItemsA19, ClassEndLabel) {
  auto r = Parse(
      "class C;\n"
      "endclass : C\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// class :final
TEST(ClassItemsA19, ClassFinal) {
  auto r = Parse(
      "class C :final;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->classes[0]->is_final);
}

}  // namespace
