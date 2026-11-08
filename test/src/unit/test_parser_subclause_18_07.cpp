#include <gtest/gtest.h>

#include "fixture_parser.h"
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

TEST(ConstrainedRandomParsing, RandomizeWithBlockRejectsFourStateEquality) {
  auto r = Parse(
      "class C;\n"
      "  rand int x, y;\n"
      "  function void test();\n"
      "    this.randomize() with { x === y; };\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "4-state equality operator is not allowed in a constraint", 4,
      "18.3"));
}

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
