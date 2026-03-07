#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserSection8, ClassWithQualifiersLocalProtected) {
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

// §8.18: local method declaration parses.
TEST(ParserA818, LocalMethodParses) {
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

// §8.18: protected property declaration parses.
TEST(ParserA818, ProtectedPropertyParses) {
  auto r = Parse(
      "class Packet;\n"
      "  protected int payload;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ASSERT_GE(r.cu->classes[0]->members.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->members[0]->is_protected);
}

// §8.18: Combining local and protected is an error.
TEST(ParserA818, LocalAndProtectedError) {
  EXPECT_FALSE(ParseOk(
      "class Packet;\n"
      "  local protected int x;\n"
      "endclass\n"));
}

// §8.18: Duplicate local qualifier is an error.
TEST(ParserA818, DuplicateLocalError) {
  EXPECT_FALSE(ParseOk(
      "class Packet;\n"
      "  local local int x;\n"
      "endclass\n"));
}

// §8.18: Duplicate protected qualifier is an error.
TEST(ParserA818, DuplicateProtectedError) {
  EXPECT_FALSE(ParseOk(
      "class Packet;\n"
      "  protected protected int x;\n"
      "endclass\n"));
}

// §8.18: Local member accessed within same class method (legal).
TEST(ParserA818, LocalAccessSameClassParses) {
  EXPECT_TRUE(ParseOk(
      "class Packet;\n"
      "  local integer i;\n"
      "  function integer compare(Packet other);\n"
      "    compare = (this.i == other.i);\n"
      "  endfunction\n"
      "endclass\n"));
}

// §8.18: Protected method in derived class parses.
TEST(ParserA818, ProtectedMethodInDerived) {
  EXPECT_TRUE(ParseOk(
      "class Base;\n"
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

// §8.18: Unqualified members are public (default).
TEST(ParserA818, UnqualifiedMembersPublic) {
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

}  // namespace
