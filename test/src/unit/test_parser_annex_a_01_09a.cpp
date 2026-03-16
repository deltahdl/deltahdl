#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ClassItemsParsing, ClassProperty) {
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

TEST(ClassItemsParsing, RandProperty) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->classes[0]->members[0]->is_rand);
}

TEST(ClassItemsParsing, RandcProperty) {
  auto r = Parse(
      "class C;\n"
      "  randc bit [2:0] x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->classes[0]->members[0]->is_randc);
}

TEST(ClassItemsParsing, StaticProperty) {
  auto r = Parse(
      "class C;\n"
      "  static int count;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->classes[0]->members[0]->is_static);
}

TEST(ClassItemsParsing, ProtectedProperty) {
  auto r = Parse(
      "class C;\n"
      "  protected int data;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->classes[0]->members[0]->is_protected);
}

TEST(ClassItemsParsing, LocalProperty) {
  auto r = Parse(
      "class C;\n"
      "  local int secret;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->classes[0]->members[0]->is_local);
}

TEST(ClassItemsParsing, ConstProperty) {
  auto r = Parse(
      "class C;\n"
      "  const int MAX = 100;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->classes[0]->members[0]->is_const);
}

TEST(ClassItemsParsing, ClassPropertyWithAttr) {
  auto r = Parse(
      "class C;\n"
      "  (* my_attr *) int x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassItemsParsing, ClassNullItem) {
  auto r = Parse(
      "class C;\n"
      "  ;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassItemsParsing, ClassLocalparam) {
  auto r = Parse(
      "class C;\n"
      "  localparam int MAX = 255;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassItemsParsing, ClassParameter) {
  auto r = Parse(
      "class C;\n"
      "  parameter int W = 8;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- Moved from test_parser_clause_08_03.cpp ---

TEST(ClassItemsParsing, ClassEmptyItem) {
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

TEST(ClassItemsParsing, BasicClassWithProperty) {
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

TEST(ClassItemsParsing, ErrorBothLocalAndProtected) {
  auto r = Parse(
      "class C;\n"
      "  local protected int x;\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ClassItemsParsing, ErrorDuplicateStatic) {
  auto r = Parse(
      "class C;\n"
      "  static static int x;\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

// --- Moved from test_parser_clause_08_05.cpp ---

TEST(ClassItemsParsing, ClassWithProperties) {
  auto r = Parse(
      "class Packet;\n"
      "  int header;\n"
      "  int payload;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 2u);
  const std::string kExpectedNames[] = {"header", "payload"};
  for (size_t i = 0; i < 2; ++i) {
    EXPECT_EQ(cls->members[i]->kind, ClassMemberKind::kProperty);
    EXPECT_EQ(cls->members[i]->name, kExpectedNames[i]);
  }
}

TEST(ClassItemsParsing, VariousPropertyDataTypes) {
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

TEST(ClassItemsParsing, MultiplePropertiesCommaSeparated) {
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

TEST(ClassItemsParsing, TwoPropertyDeclarations) {
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

TEST(ClassItemsParsing, ClassWithProperty) {
  auto r = Parse("class pkt; int data; endclass");
  ASSERT_NE(r.cu, nullptr);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->members.size(), 1);
  EXPECT_EQ(cls->members[0]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(cls->members[0]->name, "data");
  EXPECT_EQ(cls->members[0]->data_type.kind, DataTypeKind::kInt);
}

// --- Moved from test_parser_clause_08_07.cpp ---

TEST(ClassItemsParsing, ClassWithInitializer) {
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

// --- Moved from test_parser_clause_08_09.cpp ---

TEST(ClassItemsParsing, StaticPropertyDeclaration) {
  auto r = Parse(
      "class Packet;\n"
      "  static integer fileID;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 1u);
  EXPECT_EQ(cls->members[0]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(cls->members[0]->name, "fileID");
  EXPECT_TRUE(cls->members[0]->is_static);
}

TEST(ClassItemsParsing, StaticPropertyWithInitializer) {
  auto r = Parse(
      "class Packet;\n"
      "  static int count = 0;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 1u);
  EXPECT_TRUE(cls->members[0]->is_static);
  EXPECT_NE(cls->members[0]->init_expr, nullptr);
}

TEST(ClassItemsParsing, MixedStaticAndInstanceProperties) {
  auto r = Parse(
      "class C;\n"
      "  static int shared_val;\n"
      "  int inst_val;\n"
      "  static string name;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 3u);
  EXPECT_TRUE(cls->members[0]->is_static);
  EXPECT_EQ(cls->members[0]->name, "shared_val");
  EXPECT_FALSE(cls->members[1]->is_static);
  EXPECT_EQ(cls->members[1]->name, "inst_val");
  EXPECT_TRUE(cls->members[2]->is_static);
  EXPECT_EQ(cls->members[2]->name, "name");
}

// --- Moved from test_parser_clause_08_19.cpp ---

TEST(ClassItemsParsing, ConstPropertyVerifiesName) {
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

TEST(ClassItemsParsing, StaticConstProperty) {
  auto r = Parse(
      "class Config;\n"
      "  static const int VERSION = 3;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 1u);
  EXPECT_TRUE(cls->members[0]->is_static);
  EXPECT_TRUE(cls->members[0]->is_const);
}

TEST(ClassItemsParsing, ConstAndStaticConstProperties) {
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

TEST(ClassItemsParsing, ConstPropertyWithInitExpression) {
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

TEST(ClassItemsParsing, InstanceConstantNoInitializer) {
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

TEST(ClassItemsParsing, StaticConstPropertyWithInitializer) {
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

// --- Moved from test_parser_clause_08_25.cpp ---

TEST(ClassItemsParsing, ParameterMemberInClass) {
  auto r = Parse(
      "class par_cls;\n"
      "  parameter int b = 23;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "par_cls");
}

// --- Moved from test_parser_annex_a_10.cpp ---

TEST(ClassItemsParsing, ParameterInClassItem) {
  EXPECT_TRUE(
      ParseOk("class my_class;\n"
              "  parameter int WIDTH = 8;\n"
              "endclass\n"));
}

TEST(ClassItemsParsing, LocalparamInClassItem) {
  EXPECT_TRUE(
      ParseOk("class my_class;\n"
              "  localparam int WIDTH = 8;\n"
              "endclass\n"));
}

TEST(ClassItemsParsing, CovergroupInClass) {
  EXPECT_TRUE(
      ParseOk("class my_class;\n"
              "  covergroup cg;\n"
              "    coverpoint x;\n"
              "  endgroup\n"
              "  int x;\n"
              "endclass\n"));
}

// --- Missing coverage tests ---

TEST(ClassItemsParsing, PropertyWithUnpackedDimension) {
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

TEST(ClassItemsParsing, ConstProtectedProperty) {
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

TEST(ClassItemsParsing, ConstLocalProperty) {
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

TEST(ClassItemsParsing, RandProtectedProperty) {
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

TEST(ClassItemsParsing, RandStaticProperty) {
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

TEST(ClassItemsParsing, ErrorRandAndRandc) {
  auto r = Parse(
      "class C;\n"
      "  rand randc int x;\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ClassItemsParsing, ErrorDuplicateRand) {
  auto r = Parse(
      "class C;\n"
      "  rand rand int x;\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
