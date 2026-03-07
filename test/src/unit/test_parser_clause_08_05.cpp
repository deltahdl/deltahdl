#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection8, ClassWithProperties) {
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

// §8.5: Property access via dot notation.
TEST(ParserA85, PropertyAccessDotNotation) {
  auto r = Parse(
      "class Packet;\n"
      "  int command;\n"
      "  int address;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    automatic int var1;\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    p.command = 1;\n"
      "    p.address = 2;\n"
      "    var1 = p.command;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules.back();
  ASSERT_NE(mod, nullptr);
  // Verify the class has the expected properties.
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  EXPECT_EQ(cls->name, "Packet");
  ASSERT_GE(cls->members.size(), 2u);
  EXPECT_EQ(cls->members[0]->name, "command");
  EXPECT_EQ(cls->members[1]->name, "address");
}

// §8.5: No restrictions on data type of class property.
TEST(ParserA85, VariousPropertyDataTypes) {
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

// §8.5: Parameterized class with value parameters.
TEST(ParserA85, ParameterizedClassWithValueParam) {
  auto r = Parse(
      "class vector #(parameter width = 7);\n"
      "  bit [width:0] data;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  EXPECT_EQ(cls->name, "vector");
  ASSERT_GE(cls->params.size(), 1u);
  EXPECT_EQ(cls->params[0].first, "width");
}

// §8.5: Parameter access via scope resolution is legal.
TEST(ParserA85, ParameterAccessViaScope) {
  ParseOk(
      "class vector #(parameter width = 7, type T = int);\n"
      "  T data;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    automatic int w;\n"
      "    vector #(3) v;\n"
      "    v = new;\n"
      "    w = v.width;\n"
      "  end\n"
      "endmodule\n");
}

TEST(ParserSection8, MultiplePropertiesCommaSeparated) {
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

TEST(ParserClause03, Cl3_13_ClassScopeMembers) {
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

TEST(Parser, ClassWithProperty) {
  auto r = Parse("class pkt; int data; endclass");
  ASSERT_NE(r.cu, nullptr);
  auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->members.size(), 1);
  EXPECT_EQ(cls->members[0]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(cls->members[0]->name, "data");
  EXPECT_EQ(cls->members[0]->data_type.kind, DataTypeKind::kInt);
}

}  // namespace
