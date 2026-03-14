#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ConstraintItemsParsing, BasicConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c_x { x > 0; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintItemsParsing, SolveBefore) {
  auto r = Parse(
      "class C;\n"
      "  rand int x, y;\n"
      "  constraint c { solve x before y; x inside {[0:10]}; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintItemsParsing, SoftConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c_x { soft x == 5; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintItemsParsing, ImplicationConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x, y;\n"
      "  constraint c { x > 0 -> y > 0; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintItemsParsing, IfElseConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x, mode;\n"
      "  constraint c {\n"
      "    if (mode == 0) { x < 10; }\n"
      "    else { x > 100; }\n"
      "  }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintItemsParsing, ForeachConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int arr[10];\n"
      "  constraint c {\n"
      "    foreach (arr[i]) arr[i] inside {[0:255]};\n"
      "  }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintItemsParsing, DisableSoft) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c_x { soft x == 5; }\n"
      "  constraint c_override { disable soft x; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintItemsParsing, UniquenessConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int a, b, c;\n"
      "  constraint c_uniq { unique {a, b, c}; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintItemsParsing, DistConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c_x {\n"
      "    x dist { 1 := 10, [2:5] :/ 20 };\n"
      "  }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintItemsParsing, ConstraintPrototype) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c_x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintItemsParsing, ExternConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  extern constraint c_x;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintItemsParsing, StaticConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  static constraint c_x { x > 0; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintItemsParsing, MultipleConstraints) {
  auto r = Parse(
      "class C;\n"
      "  rand int x, y;\n"
      "  constraint c_x { x > 0; }\n"
      "  constraint c_y { y > 0; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->classes[0]->members.size(), 4u);
}

TEST(ConstraintItemsParsing, EmptyConstraintBlock) {
  auto r = Parse(
      "class C;\n"
      "  constraint c_empty { }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ConstraintItemsParsing, InsideConstraint) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c_x { x inside {1, 2, [5:10]}; }\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
