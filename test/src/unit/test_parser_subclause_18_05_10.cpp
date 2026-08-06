#include "fixture_parser.h"

using namespace delta;

namespace {

// Locate a constraint member of the given name within a parsed class.
const ClassMember* FindConstraint(const ClassDecl* cls, std::string_view name) {
  for (const auto* m : cls->members) {
    if (m->kind == ClassMemberKind::kConstraint && m->name == name) return m;
  }
  return nullptr;
}

// 18.5.10 (Syntax 18-9): a constraint block may be qualified 'static' by
// preceding the 'constraint' keyword with 'static'. The parser accepts the
// declaration and records the static qualification on the constraint member.
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

// 18.5.10: a constraint declared without the 'static' keyword is not static;
// the qualification is recorded only when the keyword is present.
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

// 18.5.10: a constraint prototype may also be qualified 'static'. The bodyless
// declaration is recognized as a prototype that carries the static qualifier.
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

// 18.5.10: an external constraint block completing a prototype may be qualified
// 'static'. The parser records the static qualifier on the external block.
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

// 18.5.10: an external constraint block declared without 'static' records no
// static qualification, distinguishing it from the static form.
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
