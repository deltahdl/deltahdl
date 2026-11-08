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

TEST(SoftConstraintParsing, SoftRelationCapturedAsSoftNotHard) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { soft x == 42; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->classes.empty());
  const auto* m = FindConstraint(r.cu->classes.front(), "c");
  ASSERT_NE(m, nullptr);
  EXPECT_EQ(m->constraint_soft_exprs.size(), 1u);
  EXPECT_TRUE(m->constraint_exprs.empty());
}

TEST(SoftConstraintParsing, HardAndSoftInSameBlockSeparated) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint c { x > 0; soft x == 5; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->classes.empty());
  const auto* m = FindConstraint(r.cu->classes.front(), "c");
  ASSERT_NE(m, nullptr);
  EXPECT_EQ(m->constraint_exprs.size(), 1u);
  EXPECT_EQ(m->constraint_soft_exprs.size(), 1u);
}

TEST(SoftConstraintParsing, DisableSoftOnAnArraysSizeIsRecorded) {
  auto r = Parse(
      "class D;\n"
      "  rand int v;\n"
      "endclass\n"
      "class C;\n"
      "  rand int a[];\n"
      "  rand int b[$];\n"
      "  rand D h;\n"
      "  constraint c { disable soft a.size(); disable soft b.size;\n"
      "                 disable soft h.v; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  const auto* m = FindConstraint(r.cu->classes.back(), "c");
  ASSERT_NE(m, nullptr);
  ASSERT_EQ(m->constraint_disable_soft_refs.size(), 2u);
  EXPECT_EQ(m->constraint_disable_soft_refs[0].name, "a.size");
  EXPECT_EQ(m->constraint_disable_soft_refs[1].name, "b.size");
}

}  // namespace
