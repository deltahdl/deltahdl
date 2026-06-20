#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ConstrainedRandomParsing, RandomizeWithMultipleConstraints) {
  auto r = Parse(
      "class SimpleSum;\n"
      "  rand bit [7:0] x, y, z;\n"
      "  constraint c { z == x + y; }\n"
      "  function void test();\n"
      "    this.randomize() with { x < y; x > 10; y < 200; };\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ConstrainedRandomParsing, RandomizeWithRestrictedIdList) {
  auto r = Parse(
      "class C;\n"
      "  rand integer x;\n"
      "endclass\n"
      "function int F(int y);\n"
      "  C obj;\n"
      "  F = obj.randomize() with (x) { x < y; };\n"
      "endfunction\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(SubroutineCallExprParsing, RandomizeCallWithConstraintBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin obj.randomize() with { x < 10; }; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstrainedRandomParsing, RandomizeWithIdListAndConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x, y;\n"
      "  function void test();\n"
      "    this.randomize() with (x) { x > 0; x < y; };\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

// 18.7 identifier_list ::= identifier { , identifier }: the parenthesized list
// after 'with' on an object randomize may name more than one variable.
TEST(ConstrainedRandomParsing, RandomizeWithMultiIdentifierList) {
  auto r = Parse(
      "class C;\n"
      "  rand int x, y, z;\n"
      "  function void test();\n"
      "    this.randomize() with (x, y) { x < y; y < z; };\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

// 18.7 inline_constraint_declaration admits 'null' as the random-variable
// argument of an object randomize (the `variable_identifier_list | null`
// alternative), here combined with an inline constraint block.
TEST(ConstrainedRandomParsing, RandomizeNullArgumentWithBlock) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "endclass\n"
      "function void F();\n"
      "  C obj;\n"
      "  obj.randomize(null) with { x > 0; };\n"
      "endfunction\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

}  // namespace
