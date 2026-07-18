#include "fixture_parser.h"

using namespace delta;

namespace {

// Return the first constraint member of the (single) class parsed from src.
const ClassMember* FirstConstraint(const ParseResult& r) {
  if (r.cu == nullptr || r.cu->classes.empty()) return nullptr;
  for (const auto* m : r.cu->classes[0]->members) {
    if (m->kind == ClassMemberKind::kConstraint) return m;
  }
  return nullptr;
}

// 18.5.4 / Syntax 18-4: a uniqueness_constraint ("unique { range_list }") is a
// valid constraint_expression. A group of singular variables parses cleanly and
// the parser captures the whole range_list as one uniqueness group so the
// simulator can build a kUnique solver constraint from it.
TEST(ConstraintUniqueParsing, SingularVariableGroupCaptured) {
  auto r = Parse(
      "class C;\n"
      "  rand byte a;\n"
      "  rand byte b;\n"
      "  rand byte excluded;\n"
      "  constraint u { unique {a, b, excluded}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  const ClassMember* c = FirstConstraint(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->constraint_unique_refs.size(), 1u);
  EXPECT_EQ(c->constraint_unique_refs[0].size(), 3u);
}

// 18.5.4: the range_list of a uniqueness_constraint may name an array slice
// alongside singular variables, as in the unique {b, a[2:3], excluded} example.
// All three range_list items are captured as members of the one group.
TEST(ConstraintUniqueParsing, ArraySliceMemberCaptured) {
  auto r = Parse(
      "class C;\n"
      "  rand byte a[5];\n"
      "  rand byte b;\n"
      "  rand byte excluded;\n"
      "  constraint u { unique {b, a[2:3], excluded}; }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  const ClassMember* c = FirstConstraint(r);
  ASSERT_NE(c, nullptr);
  ASSERT_EQ(c->constraint_unique_refs.size(), 1u);
  EXPECT_EQ(c->constraint_unique_refs[0].size(), 3u);
}

// 18.5.4: a constraint block may hold a uniqueness constraint next to ordinary
// relational constraints; each is captured on its own so the simulator applies
// them together. The single unique group is recorded apart from the relations.
TEST(ConstraintUniqueParsing, UniqueCapturedAlongsideRelations) {
  auto r = Parse(
      "class C;\n"
      "  rand int a;\n"
      "  rand int b;\n"
      "  constraint u {\n"
      "    a >= 0;\n"
      "    unique {a, b};\n"
      "  }\n"
      "endclass\n");
  EXPECT_FALSE(r.has_errors);
  const ClassMember* c = FirstConstraint(r);
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->constraint_unique_refs.size(), 1u);
  EXPECT_FALSE(c->constraint_exprs.empty());
}

}  // namespace
