#include <gtest/gtest.h>

#include <string_view>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_class.h"

using namespace delta;

namespace {

const ClassMember* FindConstraint(const ClassDecl* cls, std::string_view name) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kConstraint && m->name == name) return m;
  }
  return nullptr;
}

TEST(ConstraintInheritanceParsing, InitialAndExtendsRejected) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint :initial :extends c { x > 0; }\n"
      "endclass\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got 'extends'", 3, "18.5"));
}

TEST(ConstraintInheritanceParsing, InitialFinalCombinationRecorded) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint :initial :final c { x > 0; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->classes.empty());
  const auto* m = FindConstraint(r.cu->classes.front(), "c");
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_constraint_initial);
  EXPECT_TRUE(m->is_constraint_final);
}

TEST(ConstraintInheritanceParsing, ExtendsFinalCombinationRecorded) {
  auto r = Parse(
      "class C;\n"
      "  rand int x;\n"
      "  constraint :extends :final c { x > 0; }\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_FALSE(r.cu->classes.empty());
  const auto* m = FindConstraint(r.cu->classes.front(), "c");
  ASSERT_NE(m, nullptr);
  EXPECT_TRUE(m->is_constraint_extends);
  EXPECT_TRUE(m->is_constraint_final);
}

}  // namespace
