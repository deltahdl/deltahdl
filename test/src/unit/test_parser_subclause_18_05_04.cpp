#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "parser/ast_class.h"

using namespace delta;

namespace {

const ClassMember* FirstConstraint(const ParseResult& r) {
  if (r.cu == nullptr || r.cu->classes.empty()) return nullptr;
  for (const auto* m : r.cu->classes[0]->members) {
    if (m->kind == ClassMemberKind::kConstraint) return m;
  }
  return nullptr;
}

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
