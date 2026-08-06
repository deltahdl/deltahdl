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

// 18.5.2: ':initial' and ':extends' are mutually exclusive on a constraint.
// The override-specifier grammar admits at most one of them (optionally
// followed by ':final'), so a declaration that names both is rejected at parse
// time.
TEST(ConstraintInheritanceParsing, InitialAndExtendsRejected) {
  EXPECT_FALSE(
      ParseOk("class C;\n"
              "  rand int x;\n"
              "  constraint :initial :extends c { x > 0; }\n"
              "endclass\n"));
}

// 18.5.2: ':final' may be combined with ':initial'. The parser accepts the
// pairing and records both specifiers on the constraint member.
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

// 18.5.2: ':final' may be combined with ':extends'. The parser accepts the
// pairing and records both specifiers on the constraint member.
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
