#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(DataHidingParsing, ClassWithQualifiersLocalProtected) {
  auto r = Parse(
      "class MyClass;\n"
      "  local int secret;\n"
      "  protected int hidden;\n"
      "  static int shared;\n"
      "  rand int random_val;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 4u);
  EXPECT_TRUE(cls->members[0]->is_local);
  EXPECT_TRUE(cls->members[1]->is_protected);
}

TEST(DataHidingParsing, LocalMethodParses) {
  auto r = Parse(
      "class Packet;\n"
      "  local function int get_id();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ASSERT_GE(r.cu->classes[0]->members.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->members[0]->is_local);
}

TEST(DataHidingParsing, ProtectedPropertyParses) {
  auto r = Parse(
      "class Packet;\n"
      "  protected int payload;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ASSERT_GE(r.cu->classes[0]->members.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->members[0]->is_protected);
}

TEST(DataHidingParsing, LocalAndProtectedError) {
  EXPECT_FALSE(
      ParseOk("class Packet;\n"
              "  local protected int x;\n"
              "endclass\n"));
}

TEST(DataHidingParsing, DuplicateLocalError) {
  EXPECT_FALSE(
      ParseOk("class Packet;\n"
              "  local local int x;\n"
              "endclass\n"));
}

TEST(DataHidingParsing, DuplicateProtectedError) {
  EXPECT_FALSE(
      ParseOk("class Packet;\n"
              "  protected protected int x;\n"
              "endclass\n"));
}

TEST(DataHidingParsing, LocalAccessSameClassParses) {
  EXPECT_TRUE(
      ParseOk("class Packet;\n"
              "  local integer i;\n"
              "  function integer compare(Packet other);\n"
              "    compare = (this.i == other.i);\n"
              "  endfunction\n"
              "endclass\n"));
}

TEST(DataHidingParsing, ProtectedMethodInDerived) {
  EXPECT_TRUE(
      ParseOk("class Base;\n"
              "  protected function int secret();\n"
              "    return 42;\n"
              "  endfunction\n"
              "endclass\n"
              "class Derived extends Base;\n"
              "  function int get_secret();\n"
              "    return secret();\n"
              "  endfunction\n"
              "endclass\n"));
}

TEST(DataHidingParsing, UnqualifiedMembersPublic) {
  auto r = Parse(
      "class Packet;\n"
      "  int x;\n"
      "  function void f(); endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->classes[0]->members.size(), 2u);
  EXPECT_FALSE(r.cu->classes[0]->members[0]->is_local);
  EXPECT_FALSE(r.cu->classes[0]->members[0]->is_protected);
}

TEST(DataHidingParsing, ClassQualifierCombinations) {
  auto r = Parse(
      "class C;\n"
      "  static local int a;\n"
      "  protected rand int b;\n"
      "  static virtual function void sv_fn(); endfunction\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 3u);
  EXPECT_TRUE(members[0]->is_static);
  EXPECT_TRUE(members[0]->is_local);
  EXPECT_TRUE(members[1]->is_protected);
  EXPECT_TRUE(members[1]->is_rand);
  EXPECT_TRUE(members[2]->is_static);
  EXPECT_TRUE(members[2]->is_virtual);
}

TEST(DataHidingParsing, ErrorDuplicateVirtual) {
  auto r = Parse(
      "class C;\n"
      "  virtual virtual function void f(); endfunction\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(DataHidingParsing, ConstProtectedProperty) {
  auto r = Parse(
      "class C;\n"
      "  const protected int X = 10;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_const);
  EXPECT_TRUE(m->is_protected);
}

TEST(DataHidingParsing, ConstLocalProperty) {
  auto r = Parse(
      "class C;\n"
      "  const local int Y = 20;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_const);
  EXPECT_TRUE(m->is_local);
}

TEST(DataHidingParsing, RandProtectedProperty) {
  auto r = Parse(
      "class C;\n"
      "  rand protected int x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_rand);
  EXPECT_TRUE(m->is_protected);
}

TEST(DataHidingParsing, PureVirtualProtectedMethodPrototype) {
  auto r = Parse(
      "class C;\n"
      "  pure virtual protected function void work();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_protected);
}

TEST(DataHidingParsing, ProtectedMethodFunction) {
  auto r = Parse(
      "class C;\n"
      "  protected function void work();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_EQ(m->kind, ClassMemberKind::kMethod);
  EXPECT_TRUE(m->is_protected);
}

TEST(DataHidingParsing, ProtectedMethodTask) {
  auto r = Parse(
      "class C;\n"
      "  protected task run();\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_EQ(m->kind, ClassMemberKind::kMethod);
  EXPECT_TRUE(m->is_protected);
}

TEST(DataHidingParsing, LocalMethodFunction) {
  auto r = Parse(
      "class C;\n"
      "  local function void secret();\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_EQ(m->kind, ClassMemberKind::kMethod);
  EXPECT_TRUE(m->is_local);
}

TEST(DataHidingParsing, LocalMethodTask) {
  auto r = Parse(
      "class C;\n"
      "  local task secret_task();\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_EQ(m->kind, ClassMemberKind::kMethod);
  EXPECT_TRUE(m->is_local);
}

TEST(DataHidingParsing, ConstructorLocalQualifierLegal) {
  ParseOk(
      "class C;\n"
      "  local function new();\n"
      "  endfunction\n"
      "endclass\n");
}

TEST(DataHidingParsing, ConstructorProtectedQualifierLegal) {
  ParseOk(
      "class C;\n"
      "  protected function new(int x);\n"
      "  endfunction\n"
      "endclass\n");
}

TEST(DataHidingParsing, ExternProtectedMethodPrototype) {
  auto r = Parse(
      "class C;\n"
      "  extern protected function void compute();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_protected);
  EXPECT_TRUE(m->method->is_extern);
}

TEST(DataHidingParsing, ExternLocalMethodPrototype) {
  auto r = Parse(
      "class C;\n"
      "  extern local task do_work();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_local);
  EXPECT_TRUE(m->method->is_extern);
}

TEST(DataHidingParsing, ProtectedLocalError) {
  EXPECT_FALSE(
      ParseOk("class Packet;\n"
              "  protected local int x;\n"
              "endclass\n"));
}

TEST(DataHidingParsing, DuplicateConstError) {
  EXPECT_FALSE(
      ParseOk("class C;\n"
              "  const const int X = 1;\n"
              "endclass\n"));
}

TEST(DataHidingParsing, PureVirtualLocalMethodPrototype) {
  auto r = Parse(
      "class C;\n"
      "  pure virtual local function void secret();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_virtual);
  EXPECT_TRUE(m->is_local);
}

}  // namespace
