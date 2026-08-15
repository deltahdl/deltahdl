#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

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

// 18.7: the constraint block following 'with' can define all the same
// constraint forms a class constraint can -- and, being a constraint block, is
// subject to the same rules. A 4-state equality operator is illegal in any
// constraint (18.3), so it is rejected inside an inline block too. This error
// is observable only because the inline block is now captured and scanned
// rather than skipped at parse time.
TEST(ConstrainedRandomParsing, RandomizeWithBlockRejectsFourStateEquality) {
  auto r = Parse(
      "class C;\n"
      "  rand int x, y;\n"
      "  function void test();\n"
      "    this.randomize() with { x === y; };\n"
      "  endfunction\n"
      "endclass\n");
  // §18.3 owns the 4-state operator rule and files the report under itself,
  // whether the constraint block is inline or in the class.
  EXPECT_TRUE(ReportedError(
      r.diags, "4-state equality operator is not allowed in a constraint", 4,
      "18.3"));
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
