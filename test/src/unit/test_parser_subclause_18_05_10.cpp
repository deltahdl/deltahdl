#include <gtest/gtest.h>

#include <string_view>

#include "fixture_parser.h"
#include "parser/ast_class.h"

using namespace delta;

namespace {

const ClassMember* FindConstraint(const ClassDecl* cls, std::string_view name) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kConstraint && m->name == name) return m;
  }
  return nullptr;
}

TEST(StaticConstraintParsing, StaticConstraintBlockRecognized) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  static constraint c { x > 0; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->classes.empty());
  const auto* m = FindConstraint(r.cu->classes.front(), "c");
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_static);
}

TEST(StaticConstraintParsing, NonStaticConstraintBlockNotStatic) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x > 0; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->classes.empty());
  const auto* m = FindConstraint(r.cu->classes.front(), "c");
  ASSERT_NE(m, nullptr);
  EXPECT_FALSE(m->is_static);
}

TEST(StaticConstraintParsing, StaticConstraintPrototypeRecognized) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  static constraint c;\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->classes.empty());
  const auto* m = FindConstraint(r.cu->classes.front(), "c");
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_constraint_prototype);
  EXPECT_TRUE(m->is_static);
}

TEST(StaticConstraintParsing, StaticExternalBlockRecordsStatic) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  static constraint c;\n"
      "endclass\n"
      "static constraint C::c { x > 0; }\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->external_constraints.size(), 1u);
  EXPECT_TRUE(r.cu->external_constraints.front().is_static);
}

TEST(StaticConstraintParsing, NonStaticExternalBlockNotStatic) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c;\n"
      "endclass\n"
      "constraint C::c { x > 0; }\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->external_constraints.size(), 1u);
  EXPECT_FALSE(r.cu->external_constraints.front().is_static);
}

}  // namespace
